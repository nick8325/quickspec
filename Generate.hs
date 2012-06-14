{-# LANGUAGE ExistentialQuantification, Rank2Types #-}
module Generate where

import Signature
import qualified TestTree as T
import TestTree(TestResults, reps, classes, numTests, cutOff)
import Typed
import Term
import Text.Printf
import Typeable
import Utils
import Test.QuickCheck.Gen
import System.Random
import qualified Data.Map as Map
import Data.Maybe
import Control.Spoon
import Control.Monad
import System.IO
import Control.Exception
import Data.Array hiding (index)
import Unsafe.Coerce
import GHC.Prim

findWitness :: Sig -> TypeRep -> Some (K ())
findWitness sig ty =
  Map.findWithDefault
    (error "Generate.witness: type not found")
    ty (witnesses sig)

terms :: Sig -> TypeMap (C [] Term) -> TypeRep -> [Some Term]
terms sig base ty =
  app (Var . unC) (variables sig) ty ++
  app (Const . unC) (constants sig) ty ++
  [ Some (App (cast' f) x `asTypeOf` witness y)
  | lhs <- argTypes sig ty,
    Some x <- app id base lhs, 
    not (isUndefined x), 
    Some f <- terms sig base (mkFunTy lhs ty),
    not (isUndefined f), 
    Some y <- [findWitness sig ty] ]
  
  where app :: (forall a. f a -> g a) ->
                 TypeMap (C [] f) ->
                 TypeRep ->
                 [Some g]
        app f x ty =
          case Map.lookup ty x of
            Nothing -> []
            Just (Some (C xs)) ->
              [ Some (f x) | x <- xs ]
              
        witness :: K () a -> Term a
        witness _ = undefined
        
        cast' x = fromMaybe (error "Generate.terms: type error") (cast x)

unbuffered :: IO a -> IO a
unbuffered x = do
  buf <- hGetBuffering stdout
  bracket_
    (hSetBuffering stdout NoBuffering)
    (hSetBuffering stdout buf)
    x

generate :: Sig -> IO (TypeMap (C TestResults Term))
generate Sig { maxDepth = n } | n < 0 =
  error "Generate.generate: maxDepth must be positive"
generate Sig { maxDepth = 0 } = return Typed.empty
generate sig = unbuffered $ do
  let d = maxDepth sig
  rs <- fmap (mapValues (C . reps . unC)) (generate sig { maxDepth = d - 1})
  printf "Depth %d: " d
  let count :: ([a] -> a) -> (forall b. f (g b) -> a) ->
               TypeMap (C f g) -> a
      count op f = op . map (Typed.some (f . unC)) . Typed.toList
      ts = Typed.fromList [ gather (terms sig rs ty) | ty <- testableTypes sig ]
  printf "%d terms, " (count sum length ts)
  seeds <- genSeeds
  let cs = fmap (mapSome (C . test seeds sig . unC)) ts
  printf "%d tests, %d classes, %d raw equations.\n"
      (count (maximum . (0:)) numTests cs)
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
          val = memoSym sig (unGen valuation g1 n) in
      teaspoon . force . unGen x g2 n . eval val
    force x = x == x `seq` x

memoSym :: Sig -> (forall a. Var a -> a) -> (forall a. Var a -> a)
memoSym sig f = unsafeCoerce . (arr !) . index
  where arr :: Array Int Any
        arr = array (0, maximum (0:map index (names (variables sig))))
                [(index v, unsafeCoerce (f v))
                | Some (C vs) <- Typed.toList (variables sig),
                  C v <- vs]
