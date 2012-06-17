-- | A data structure to represent refining a set of terms into
--   equivalence classes by testing.

module Test.QuickSpec.TestTree(TestTree, terms, union, test,
               TestResults, cutOff, numTests, classes, reps) where

import Data.List(sort)
import Test.QuickSpec.Utils
import Control.Exception(assert)
import Control.Parallel.Strategies

-- Invariant: the children of a TestTree are sorted according to the
-- parent's test. We exploit this in defining merge.
--
-- A TestTree is always infinite, and branches t is always a
-- refinement of t (it may be trivial, so that length (branches t) == 1).
-- As a special case, a TestTree may be Nil, but Nil may not appear in
-- the branches of a TestTree.
data TestTree a = Nil | NonNil (TestTree' a)
data TestTree' a = Tree { rep :: a, rest :: [a], branches :: [TestTree' a] }

-- Precondition: bs must be sorted according to the TestCase.
tree :: Ord r => [a] -> (a -> r) -> [TestTree' a] -> TestTree' a
tree [] _ _ =
  error "Test.QuickSpec.TestTree.tree: bug: empty equivalence class"
tree (x:xs) eval bs =
  assert (isSortedBy (eval . rep) bs) $
    Tree { rep = x, rest = xs, branches = bs }

terms :: TestTree a -> [a]
terms Nil = []
terms (NonNil t) = terms' t

terms' :: TestTree' a -> [a]
terms' Tree{rep = x, rest = xs} = x:xs

-- Precondition: the sequence of test cases given must be
-- that used to generate the two TestTrees.
union :: Ord r => [a -> r] -> TestTree a -> TestTree a -> TestTree a
union _ Nil t = t
union _ t Nil = t
union evals (NonNil t1) (NonNil t2) = NonNil (union' evals t1 t2)

union' :: Ord r => [a -> r] -> TestTree' a -> TestTree' a -> TestTree' a
union' (eval:evals) t1 t2 =
  tree (terms' t1 ++ terms' t2) eval
         (merge (union' evals) (eval . rep) (branches t1) (branches t2))

test :: Ord r => [a -> r] -> [a] -> TestTree a
test _ [] = Nil
test tcs xs = NonNil (test' tcs xs)

test' :: Ord r => [a -> r] -> [a] -> TestTree' a
test' [] _ =
  error "Test.QuickSpec.TestTree.test': ran out of test cases"
test' (tc:tcs) xs = tree xs tc (map (test' tcs) bs)
  where bs = partitionBy tc xs

-- A TestTree with finite depth, represented as a TestTree where some
-- nodes have no branches. Since this breaks one of the TestTree
-- invariants we use a different type.
newtype TestResults a = Results (TestTree a)

cutOff :: Int -> Int -> TestTree a -> TestResults a
cutOff _ _ Nil = Results Nil
cutOff m n (NonNil t) = Results (NonNil (aux m t))
  where aux 0 t = aux' False n n t
        aux m t = t { branches = map (aux (m-1)) (branches t) }
        -- Exponential backoff if we carry on refining a class
        aux' True 0 n t = t { branches = map (aux' False (n*2-1) (n*2)) (branches t) }
        aux' False 0 n t = t { branches = [] }
        aux' x m n t@Tree{branches = [t']} = t { branches = [aux' x (m-1) n t'] }
        aux' _ m n t = t { branches = map (aux' True (m-1) n) (branches t) }

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
