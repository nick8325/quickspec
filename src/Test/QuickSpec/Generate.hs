-- | The testing loop and term generation of QuickSpec.

{-# LANGUAGE CPP, Rank2Types, TypeOperators, ScopedTypeVariables #-}
module Test.QuickSpec.Generate where

#include "errors.h"
import Test.QuickSpec.Signature hiding (con)
import qualified Test.QuickSpec.TestTree as T
import Test.QuickSpec.TestTree(TestResults, reps, classes, numTests, numResults, cutOff, discrete)
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.TypeRel(TypeRel)
import qualified Test.QuickSpec.Utils.TypeRel as TypeRel
import Test.QuickSpec.Utils.TypeMap(TypeMap)
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import Test.QuickSpec.Term
import Text.Printf
import Test.QuickSpec.Utils.Typeable
import Test.QuickSpec.Utils
import Test.QuickCheck.Gen
import System.Random
import Control.Spoon
import Test.QuickSpec.Utils.MemoValuation

terms :: Sig -> TypeRel Expr -> TypeRel Expr
terms sig base =
  TypeMap.fromList
    [ Some (O (terms' sig base w))
    | Some (Witness w) <- usort (saturatedTypes sig ++ variableTypes sig) ]

terms' :: Typeable a => Sig -> TypeRel Expr -> a -> [Expr a]
terms' sig base w =
  map var (TypeRel.lookup w (variables sig)) ++
  map con (TypeRel.lookup w (constants sig)) ++
  [ app f x
  | Some (Witness w') <- lhsWitnesses sig w,
    x <- TypeRel.lookup w' base,
    not (isUndefined (term x)),
    f <- terms' sig base (const w),
    arity f > 0,
    not (isUndefined (term f)) ]

test :: [(Valuation, StdGen, Int)] -> Sig ->
        TypeMap (List `O` Expr) -> TypeMap (TestResults `O` Expr)
test vals sig ts = fmap (mapSome2 (test' vals sig)) ts

test' :: forall a. Typeable a =>
         [(Valuation, StdGen, Int)] -> Sig -> [Expr a] -> TestResults (Expr a)
test' vals sig ts
  | not (testable sig (undefined :: a)) = discrete ts
  | otherwise =
    case observe undefined sig of
      Observer obs ->
        let testCase (val, g, n) x =
              spoony . unGen (partialGen obs) g n $ eval x val
        in cutOff base increment (T.test (map testCase vals) ts)
  where
    base = minTests sig `div` 2
    increment = minTests sig - base

genSeeds :: Int -> IO [(StdGen, Int)]
genSeeds maxSize = do
  rnd <- newStdGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..maxSize])))

toValuation :: Strategy -> Sig -> (StdGen, Int) -> (Valuation, StdGen, Int)
toValuation strat sig (g, n) =
  let (g1, g2) = split g
  in (memoValuation sig (unGen (valuation strat) g1 n), g2, n)

generate :: Strategy -> Sig -> IO (TypeMap (TestResults `O` Expr))
generate strat sig | maxDepth sig < 0 =
  ERROR "generate: maxDepth must be positive"
generate strat sig | maxDepth sig == 0 = return TypeMap.empty
generate strat sig = unbuffered $ do
  let d = maxDepth sig
  rs <- fmap (TypeMap.mapValues2 reps) (generate (const partialGen) (updateDepth (d-1) sig))
  printf "Depth %d: " d
  let count :: ([a] -> a) -> (forall b. f (g b) -> a) ->
               TypeMap (f `O` g) -> a
      count op f = op . map (some2 f) . TypeMap.toList
      ts = terms sig rs
  printf "%d terms, " (count sum length ts)
  seeds <- genSeeds (maxQuickCheckSize sig)
  let cs = test (map (toValuation strat sig) seeds) sig ts
  printf "%d tests, %d evaluations, %d classes, %d raw equations.\n"
      (count (maximum . (0:)) numTests cs)
      (count sum numResults cs)
      (count sum (length . classes) cs)
      (count sum (sum . map (subtract 1 . length) . classes) cs)
  return cs

eraseClasses :: TypeMap (TestResults `O` Expr) -> [[Tagged Term]]
eraseClasses = concatMap (some (map (map (tagged term)) . classes . unO)) . TypeMap.toList
