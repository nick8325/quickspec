{-# LANGUAGE Rank2Types, TypeOperators #-}
module Test.QuickSpec.Generate where

import Test.QuickSpec.Signature hiding (con)
import qualified Test.QuickSpec.TestTree as T
import Test.QuickSpec.TestTree(TestResults, reps, classes, numTests, cutOff)
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
import Data.Maybe

terms :: Sig -> TypeRel Expr -> TypeRel Expr
terms sig base =
  TypeMap.fromList
    [ Some (O (terms' sig base w))
    | Some (Witness w) <- saturatedTypes sig,
      testable sig w ]

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

test :: [(StdGen, Int)] -> Sig ->
        TypeMap (List `O` Expr) -> TypeMap (TestResults `O` Expr)
test seeds sig ts = fmap (mapSome2 (test' seeds sig)) ts

test' :: Typeable a => [(StdGen, Int)] -> Sig -> [Expr a] -> TestResults (Expr a)
test' seeds sig ts =
  case observe undefined sig of
    Observer obs ->
      let testCase (g, n) =
            let (g1, g2) = split g
                val = memoValuation sig (unGen valuation g1 n) in
            \x -> teaspoon . force . unGen obs g2 n $ eval x val
          force x = x == x `seq` x
      in cutOff 100 100 (T.test (map testCase seeds) ts)

genSeeds :: IO [(StdGen, Int)]
genSeeds = do
  rnd <- newStdGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..20])))

generate :: Sig -> IO (TypeMap (TestResults `O` Expr))
generate sig | maxDepth sig < 0 =
  error "Test.QuickSpec.Generate.generate: maxDepth must be positive"
generate sig | maxDepth sig == 0 = return TypeMap.empty
generate sig = unbuffered $ do
  let d = maxDepth sig
  rs <- fmap (TypeMap.mapValues2 reps) (generate (updateDepth (d-1) sig))
  printf "Depth %d: " d
  let count :: ([a] -> a) -> (forall b. f (g b) -> a) ->
               TypeMap (f `O` g) -> a
      count op f = op . map (some2 f) . TypeMap.toList
      ts = terms sig rs
  printf "%d terms, " (count sum length ts)
  seeds <- genSeeds
  let cs = test seeds sig ts
  printf "%d tests, %d classes, %d raw equations.\n"
      (count (maximum . (0:)) numTests cs)
      (count sum (length . classes) cs)
      (count sum (sum . map (subtract 1 . length) . classes) cs)
  return cs
