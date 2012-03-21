{-# LANGUAGE FlexibleContexts, TypeFamilies #-}
module TestTree(Eval(..), TestTree, terms, union, test,
               filter, TestResults, cutOff, numTests, classes, reps) where

import Prelude hiding (filter)
import Data.List(sort)
import Utils
import Control.Exception(assert)

-- Invariant: the children of a TestTree are sorted according to the
-- parent's testCase. We exploit this in defining merge.
-- 
-- A TestTree is always infinite, and branches t is always a
-- refinement of t (it may be trivial, so that length (branches t) == 1).
-- As a special case, a TestTree may be Nil, but Nil may not appear in
-- the branches of a TestTree.
data TestTree a = Nil | NonNil (InnerTestTree a)
data InnerTestTree a = Tree { rep :: a, rest :: [a], testCase :: TestCase a, branches :: [InnerTestTree a] }

class Ord (Result a) => Eval a where
  type TestCase a
  type Result a
  eval :: TestCase a -> a -> Result a

-- Precondition: xs must be sorted, and bs must be sorted according to
-- the TestCase.
tree :: (Ord a, Eval a) => [a] -> TestCase a -> [InnerTestTree a] -> InnerTestTree a
tree [] _ _ = error "TestTree.tree: bug: empty equivalence class"
tree (x:xs) tc bs =
  assert (isSortedBy (eval tc . rep) bs) $
  assert (isSorted xs) $
    Tree { rep = x, rest = xs, testCase = tc, branches = bs }

terms :: TestTree a -> [a]
terms Nil = []
terms (NonNil t) = terms' t

terms' :: InnerTestTree a -> [a]
terms' Tree{rep = x, rest = xs} = x:xs

union :: (Ord a, Eval a) => TestTree a -> TestTree a -> TestTree a
Nil `union` t = t
t `union` Nil = t
NonNil t1 `union` NonNil t2 = NonNil (t1 `union'` t2)

union' :: (Ord a, Eval a) => InnerTestTree a -> InnerTestTree a -> InnerTestTree a
t1 `union'` t2 =
  tree (merge const id (terms' t1) (terms' t2)) (testCase t1)
       (merge union' (eval (testCase t1) . rep) (branches t1) (branches t2))

test :: (Ord a, Eval a) => [TestCase a] -> [a] -> TestTree a
test _ [] = Nil
test tcs xs = NonNil (test' tcs (sort xs))

-- Precondition: the list of terms must be sorted.
test' :: (Ord a, Eval a) => [TestCase a] -> [a] -> InnerTestTree a
test' [] _ = error "bug: ran out of test cases"
test' (tc:tcs) xs = assert (isSorted xs) $
                   -- Too clever by half trick (hence the above assert):
                   -- sort is stable, so each b <- bs is sorted
                   -- according to the usual Ord order.
                   tree xs tc (map (test' tcs) bs)
  where bs = partitionBy (eval tc) xs

-- Ignore some testcases (useful for conditional equations?)
filter :: (Ord a, Eval a) => (TestCase a -> Bool) -> TestTree a -> TestTree a
filter _ Nil = Nil
filter p (NonNil t) = NonNil (filter' p t)

filter' :: (Ord a, Eval a) => (TestCase a -> Bool) -> InnerTestTree a -> InnerTestTree a
filter' p t | p (testCase t) = t { branches = bs }
            | otherwise = foldr1 union' bs
  where bs = map (filter' p) (branches t)

-- A TestTree with finite depth, represented as a TestTree where some
-- nodes have no branches. Since this breaks one of the TestTree
-- invariants we use a different type.
newtype TestResults a = Results (TestTree a)

cutOff :: Int -> TestTree a -> TestResults a
cutOff _ Nil = Results Nil
cutOff n (NonNil t) = Results (NonNil (aux n t))
  where aux 0 t = t { branches = [] }
        aux m t@Tree{branches = [t']} = t { branches = [aux (m-1) t'] }
        aux _ t = t { branches = map (aux n) (branches t) }

numTests :: TestResults a -> Int
numTests (Results Nil) = 0
numTests (Results (NonNil t)) = aux t
  where aux Tree{branches = []} = 0
        aux Tree{branches = bs} = 1 + maximum (map aux bs)

classes :: TestResults a -> [[a]]
classes (Results Nil) = []
classes (Results (NonNil t)) = aux t
  where aux Tree{rep = x, rest = xs, branches = []} = [x:xs]
        aux Tree{branches = bs} = concatMap aux bs

reps :: TestResults a -> [a]
reps = map head . classes
