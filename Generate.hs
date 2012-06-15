{-# LANGUAGE Rank2Types, TypeOperators #-}
module Generate where

import Signature hiding (var, con)
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
import Control.Spoon
import MemoValuation

terms :: Typeable a => Sig -> TypeRel Expr -> a -> [Expr a]
terms sig base w =
  map var (TypeRel.lookup w (variables sig)) ++
  map con (TypeRel.lookup w (constants sig)) ++
  [ app f x
  | Some lhs <- map (findWitness sig) (argTypes sig (typeOf w)),
    let w' = witness lhs,
    x <- TypeRel.lookup w' base,
    not (isUndefined (term x)),
    f <- terms sig base (const w),
    not (isUndefined (term f)) ]

generate :: Sig -> IO (TypeMap (TestResults `O` Expr))
generate sig = generate' (maxDepth sig) sig

generate' d sig | d < 0 =
  error "Generate.generate: maxDepth must be positive"
generate' 0 sig = return TypeMap.empty
generate' d sig = unbuffered $ do
  rs <- fmap (TypeMap.mapValues2 reps) (generate' (d - 1) sig)
  printf "Depth %d: " d
  let count :: ([a] -> a) -> (forall b. f (g b) -> a) ->
               TypeMap (f `O` g) -> a
      count op f = op . map (Typed.some2 f) . TypeMap.toList
      ts = TypeMap.fromList
             [ Some (O (terms sig rs (witness x)))
             | ty <- testableTypes sig, 
               Some x <- [findWitness sig ty] ]
  printf "%d terms, " (count sum length ts)
  seeds <- genSeeds
  let cs = fmap (mapSome2 (test seeds sig)) ts
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

test :: Typeable a => [(StdGen, Int)] -> Sig -> [Expr a] -> TestResults (Expr a)
test seeds sig ts = test' seeds sig ts (observe undefined sig)

test' :: Typeable a => [(StdGen, Int)] -> Sig -> [Expr a] -> Observer a -> TestResults (Expr a)
test' seeds sig ts (Observer obs) = cutOff 200 (T.test (map testCase seeds) ts)
  where
    testCase (g, n) =
      let (g1, g2) = split g
          val = memoValuation sig (unGen valuation g1 n) in
      \x -> teaspoon . force . unGen obs g2 n $ eval x val
    force x = x == x `seq` x
