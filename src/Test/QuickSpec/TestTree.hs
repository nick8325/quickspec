-- | A data structure to represent refining a set of terms into
--   equivalence classes by testing.

{-# LANGUAGE CPP #-}
module Test.QuickSpec.TestTree(TestTree, terms, union, test,
               TestResults, cutOff, numTests, numResults,
               classes, reps, discrete) where

#include "errors.h"
import Data.List(sort)
import Test.QuickSpec.Utils
import Control.Exception(assert)

-- Invariant: the children of a TestTree are sorted according to the
-- parent's test. We exploit this in defining merge.
--
-- A TestTree is always infinite, and branches t is always a
-- refinement of t (it may be trivial, so that length (branches t) == 1).
data TestTree a =
  Tree {
    rep :: a,
    rest :: [a],
    branches :: [TestTree a] }

-- Precondition: bs must be sorted according to the TestCase.
tree :: Ord r => [a] -> (a -> r) -> [TestTree a] -> TestTree a
tree [] _ _ = ERROR "empty equivalence class"
tree (x:xs) eval bs =
  assert (isSortedBy (eval . rep) bs) $
    Tree { rep = x, rest = xs, branches = bs }

terms :: TestTree a -> [a]
terms Tree{rep = x, rest = xs} = x:xs

-- Precondition: the sequence of test cases given must be
-- that used to generate the two TestTrees.
union :: Ord r => [a -> r] -> TestTree a -> TestTree a -> TestTree a
union (eval:evals) t1 t2 =
  tree (terms t1 ++ terms t2) eval
    (merge (union evals) (eval . rep)
      (branches t1) (branches t2))

test :: Ord r => [a -> r] -> [a] -> TestTree a
test []       _      = ERROR "ran out of test cases"
test (_:_) []        = ERROR "found an empty equivalence class"
test (tc:tcs) xs@[_] = tree xs tc [test tcs xs]
test (tc:tcs) xs     = tree xs tc (map (test tcs) bs)
  where
    bs = partitionBy tc xs

-- A TestTree with finite depth, represented as a TestTree where some
-- nodes have no branches. Since this breaks one of the TestTree
-- invariants we use a different type.
newtype TestResults a = Results (TestTree a)

discrete :: Ord a => [a] -> TestResults a
discrete [] = ERROR "empty list"
discrete xs =
  Results (Tree y ys (map singleton (y:ys)))
  where
    y:ys = sort xs
    singleton x = Tree x [] []

cutOff :: Int -> Int -> TestTree a -> TestResults a
cutOff m n t = Results (aux m t)
  where
    aux _ t@Tree{rest = []} =
      t { branches = [] }
    aux 0 t =
      aux' False n n t
    aux m t =
      t { branches = map (aux (m-1)) (branches t) }
    -- Exponential backoff if we carry on refining a class
    aux' _ _ _ t@Tree{rest = []} =
      t { branches = [] }
    aux' True 0 n t =
      t { branches = map (aux' False (n*2-1) (n*2)) (branches t) }
    aux' False 0 _n t =
      t { branches = [] }
    aux' x m n t@Tree{branches = [t']} =
      t { branches = [aux' x (m-1) n t'] }
    aux' _ m n t =
      t { branches = map (aux' True (m-1) n) (branches t) }

numTests :: TestResults a -> Int
numTests (Results t) = aux t
  where
    aux Tree{branches = []} = 0
    aux Tree{branches = bs} = 1 + maximum (map aux bs)

numResults :: TestResults a -> Int
numResults (Results t) = aux t
  where
    aux Tree{rest = []} = 0
    aux Tree{rest = xs, branches = ts} =
      1 + length xs + sum (map aux ts)

classes :: Ord a => TestResults a -> [[a]]
classes = sort . map sort . unsortedClasses

unsortedClasses :: TestResults a -> [[a]]
unsortedClasses (Results t) = aux t
  where
    aux Tree{rep = x, rest = xs, branches = []} = [x:xs]
    aux Tree{branches = bs} = concatMap aux bs

reps :: Ord a => TestResults a -> [a]
reps = map head . classes
