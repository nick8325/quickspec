{-# LANGUAGE ExistentialQuantification, Rank2Types #-}
module Generate where

import Signature
import qualified TestTree as T
import TestTree(TestResults, reps, classes, numTests, cutOff)
import Typed
import Term
import Text.Printf
import Data.Typeable
import Utils
import Test.QuickCheck.Gen
import System.Random
import qualified Data.Map as Map
import Data.Maybe
import Control.Spoon

inhabitedTypes :: Sig -> [TypeRep]
inhabitedTypes = usort . concatMap closure . types

closure :: TypeRep -> [TypeRep]
closure ty =
  ty:
  case arrow ty of
    Nothing -> []
    Just (a, b) -> closure b

argTypes sig ty =
  [ ty1 | (ty1, ty2) <- catMaybes (map arrow (inhabitedTypes sig)), ty2 == ty ]

terms :: Sig -> TypeMap (C [] Term) -> TypeRep -> [Some Term]
terms sig base ty =
  app (Var . unC) (variables sig) ty ++
  app (Const . unC) (constants sig) ty ++
  [ fromMaybe (error "Generate.terms: type error")
      (apply App f x)
  | lhs <- argTypes sig ty,
    Some x <- app id base lhs, 
    not (isUndefined x), 
    Some f <- terms sig base (mkFunTy lhs ty),
    not (isUndefined f) ]
  
  where app :: (forall a. f a -> g a) ->
                 TypeMap (C [] f) ->
                 TypeRep ->
                 [Some g]
        app f x ty =
          case Map.lookup ty x of
            Nothing -> []
            Just (Some (C xs)) ->
              [ Some (f x) | x <- xs ]
        
generate :: Sig -> Int -> IO (TypeMap (C TestResults Term))
generate sig n | n < 0 = error "Generate.generate: depth must be positive"
generate sig 0 = return Typed.empty
generate sig d = do
  rs <- fmap (mapValues (C . reps . unC)) (generate sig (d-1))
  printf "Depth %d: " d
  let count :: ([a] -> a) -> (forall b. f (g b) -> a) ->
               TypeMap (C f g) -> a
      count op f = op . map (Typed.some (f . unC)) . Typed.toList
      ts = Typed.fromList [ Typed.sequence (terms sig rs ty) | ty <- inhabitedTypes sig ]
  printf "%d terms, " (count sum length ts)
  seeds <- genSeeds
  let cs = fmap (mapSome (C . test seeds sig . unC)) ts
  printf "%d tests, %d classes, %d raw equations.\n"
      (count maximum numTests cs)
      (count sum (length . classes) cs)
      (count sum (sum . map (subtract 1 . length) . classes) cs)
  return cs

genSeeds :: IO [(StdGen, Int)]
genSeeds = do
  rnd <- newStdGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..20])))

observe :: Typeable a => a -> Sig -> Observer a
observe x sig =
  Typed.lookup (Typed.lookup (error msg) x (ords sig))
               x (observers sig)
  where msg = "No way of observing values of type " ++ show (typeOf x)

test :: Typeable a => [(StdGen, Int)] -> Sig -> [Term a] -> TestResults (Term a)
test seeds sig ts = test' seeds sig ts (observe undefined sig)

test' :: Typeable a => [(StdGen, Int)] -> Sig -> [Term a] -> Observer a -> TestResults (Term a)
test' seeds sig ts (Observer x) = cutOff 200 (T.test (map testCase seeds) ts)
  where
    testCase (g, n) =
      let (g1, g2) = split g
          val = unGen valuation g1 n in
      teaspoon . unGen x g2 n . eval val
