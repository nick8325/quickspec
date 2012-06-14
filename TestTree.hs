{-# LANGUAGE ExistentialQuantification #-}
module TestTree(TestTree, terms, union, test,
               TestResults, cutOff, numTests, classes, reps) where

import Data.List(sort)
import Utils
import Control.Exception(assert)
import Control.Parallel.Strategies

-- Invariant: the children of a TestTree are sorted according to the
-- parent's test. We exploit this in defining merge.
-- 
-- A TestTree is always infinite, and branches t is always a
-- refinement of t (it may be trivial, so that length (branches t) == 1).
-- As a special case, a TestTree may be Nil, but Nil may not appear in
-- the branches of a TestTree.
data TestTree r a = Nil | NonNil (TestTree' r a)
data TestTree' r a = Tree { rep :: a, rest :: [a], eval :: a -> r, branches :: [TestTree' r a] }

-- Precondition: bs must be sorted according to the TestCase.
tree :: Ord r => [a] -> (a -> r) -> [TestTree' r a] -> TestTree' r a
tree [] _ _ = error "TestTree.tree: bug: empty equivalence class"
tree (x:xs) eval bs =
  assert (isSortedBy (eval . rep) bs) $
    Tree { rep = x, rest = xs, eval = eval, branches = bs }

terms :: TestTree r a -> [a]
terms Nil = []
terms (NonNil t) = terms' t

terms' :: TestTree' r a -> [a]
terms' Tree{rep = x, rest = xs} = x:xs

-- Precondition: the two test trees must have an identical sequence of test cases.
union :: Ord r => TestTree r a -> TestTree r a -> TestTree r a
Nil `union` t = t
t `union` Nil = t
NonNil t1 `union` NonNil t2 = NonNil (t1 `union'` t2)

union' :: Ord r => TestTree' r a -> TestTree' r a -> TestTree' r a
t1 `union'` t2 =
  tree (terms' t1 ++ terms' t2) (eval t1)
         (merge union' (eval t1 . rep) (branches t1) (branches t2))

test :: Ord r => [a -> r] -> [a] -> TestTree r a
test _ [] = Nil
test tcs xs = NonNil (test' tcs xs)

test' :: Ord r => [a -> r] -> [a] -> TestTree' r a
test' [] _ = error "bug: ran out of test cases"
test' (tc:tcs) xs = tree xs tc (map (test' tcs) bs)
  where bs = partitionBy tc xs

-- A TestTree with finite depth, represented as a TestTree where some
-- nodes have no branches. Since this breaks one of the TestTree
-- invariants we use a different type.
data TestResults a = forall r. Results (TestTree r a)

cutOff :: Int -> TestTree r a -> TestResults a
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

classes :: Ord a => TestResults a -> [[a]]
classes = sort . map sort . unsortedClasses

unsortedClasses :: TestResults a -> [[a]]
unsortedClasses (Results Nil) = []
unsortedClasses (Results (NonNil t)) = aux t
  where aux Tree{rep = x, rest = xs, branches = []} = [x:xs]
        aux Tree{branches = bs} = concat (parMap rseq aux bs)

reps :: Ord a => TestResults a -> [a]
reps = map head . classes
