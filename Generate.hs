{-# LANGUAGE Rank2Types #-}
module Generate where

import Signature
import qualified TestTree as T
import TestTree(TestResults, reps, classes, numTests, cutOff)
import Typed
import TypeRel(TypeRel)
import qualified TypeRel
import TypeMap(TypeMap)
import qualified TypeMap
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

findWitness :: Sig -> TypeRep -> Witness
findWitness sig ty =
  Map.findWithDefault
    (error $ "Generate.witness: type " ++ show ty ++ " not found")
    ty (witnesses sig)

terms :: Typeable a => Sig -> TypeRel Term -> a -> [Term a]
terms sig base w =
  map (Var . unC) (TypeRel.lookup w (variables sig)) ++
  map (Const . unC) (TypeRel.lookup w (constants sig)) ++
  [ App f x
  | Some lhs <- map (findWitness sig) (argTypes sig (typeOf w)),
    let w' = witness lhs,
    x <- TypeRel.lookup w' base,
    not (isUndefined x), 
    f <- terms sig base (w' `witnessArrow` w),
    not (isUndefined f) ]

unbuffered :: IO a -> IO a
unbuffered x = do
  buf <- hGetBuffering stdout
  bracket_
    (hSetBuffering stdout NoBuffering)
    (hSetBuffering stdout buf)
    x

generate :: Sig -> IO (TypeMap (C TestResults Term))
generate sig = generate' (maxDepth sig) sig

generate' d sig | d < 0 =
  error "Generate.generate: maxDepth must be positive"
generate' 0 sig = return TypeMap.empty
generate' d sig = unbuffered $ do
  rs <- fmap (TypeMap.mapValues (C . reps . unC)) (generate' (d - 1) sig)
  printf "Depth %d: " d
  let count :: ([a] -> a) -> (forall b. f (g b) -> a) ->
               TypeMap (C f g) -> a
      count op f = op . map (Typed.some (f . unC)) . TypeMap.toList
      ts = TypeMap.fromList
             [ Some (C (terms sig rs (witness x)))
             | ty <- testableTypes sig, 
               Some x <- [findWitness sig ty] ]
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
  TypeMap.lookup (TypeMap.lookup (error msg) x (ords sig))
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
                | Some (C v) <- TypeRel.toList (variables sig) ]
