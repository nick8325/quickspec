-- | A data structure to represent refining a set of terms into
--   equivalence classes by testing.

{-# LANGUAGE CPP #-}
module Test.QuickSpec.TestTree(
  TestTree, terms, union, test,
  cutOff, numTests, numResults, find) where

#include "errors.h"
import Test.QuickSpec.Utils
import Control.Exception(assert)

-- Invariant: the children of a TestTree are sorted according to the
-- parent's test. We exploit this in defining merge.
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
union [] t1 t2 = union (repeat (const ())) t1 t2
union (eval:evals) t1 t2 =
  tree (terms t1 ++ terms t2) eval
    (merge (union evals) (eval . rep)
      (branches t1) (branches t2))

test :: Ord r => [a -> r] -> [a] -> TestTree a
test []       xs     = tree xs (__ :: a -> ()) []
test (_:_) []        = ERROR "found an empty equivalence class"
test (tc:tcs) xs@[_] = tree xs tc [test tcs xs]
test (tc:tcs) xs     = tree xs tc (map (test tcs) bs)
  where
    bs = partitionBy tc xs

-- Cuts off a test tree at a certain depth to produce a finite test tree.
cutOff :: Int -> TestTree a -> TestTree a
cutOff 0 t = t { branches = [] }
cutOff n t = t { branches = map (cutOff (n-1)) (branches t) }

numTests :: TestTree a -> Int
numTests Tree{branches = []} = 0
numTests Tree{branches = bs} = 1 + maximum (map numTests bs)

numResults :: TestTree a -> Int
numResults Tree{rest = []} = 0
numResults Tree{rest = xs, branches = ts} =
  1 + length xs + sum (map numResults ts)

find :: Ord a => a -> TestTree a -> [a]
find _x t@Tree{branches = []} = terms t
find x Tree{branches = bs} = find x (head (filter p bs))
  where
    p t = x `elem` terms t
