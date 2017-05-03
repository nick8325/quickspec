-- Decision trees for testing terms for equality.
{-# LANGUAGE RecordWildCards #-}
module QuickSpec.Test.DecisionTree where

import Control.Monad
import Data.Constraint
import qualified Data.Map as Map
import Data.Map(Map)
import QuickSpec.Type
import QuickSpec.Term
import Data.Functor.Identity

data DecisionTree testcase result term =
  DecisionTree {
    -- A function for evaluating terms on test cases.
    dt_evaluate :: term -> testcase -> result,
    -- The set of test cases gathered so far.
    dt_test_cases :: [testcase],
    -- The tree itself.
    dt_tree :: !(Maybe (InnerTree result term)) }

data InnerTree result term =
    TestCase !(Map result (InnerTree result term))
  | Singleton !term

data Result testcase result term =
    Distinct (DecisionTree testcase result term)
  | EqualTo term

-- Make a new decision tree.
empty :: (term -> testcase -> result) -> DecisionTree testcase result term
empty eval =
  DecisionTree {
    dt_evaluate = eval,
    dt_test_cases = [],
    dt_tree = Nothing }

-- Add a new test case to a decision tree.
addTestCase ::
  testcase -> DecisionTree testcase result term ->
  DecisionTree testcase result term
addTestCase tc dt@DecisionTree{..} =
  dt{dt_test_cases = dt_test_cases ++ [tc]}

-- Insert a value into a decision tree.
insert :: Ord result =>
  term -> DecisionTree testcase result term ->
  Result testcase result term
insert x dt@DecisionTree{dt_tree = Nothing, ..} =
  Distinct dt{dt_tree = Just (Singleton x)}
insert x dt@DecisionTree{dt_tree = Just dt_tree, ..} =
  aux k dt_test_cases dt_tree
  where
    k tree = dt{dt_tree = Just tree}
    aux _ [] (Singleton y) = EqualTo y
    aux k (t:ts) (Singleton y) =
      aux k (t:ts) $
        TestCase (Map.singleton (dt_evaluate y t) (Singleton y)) 
    aux k (t:ts) (TestCase res) =
      let
        val = dt_evaluate x t
        k' tree = k (TestCase (Map.insert val tree res))
      in case Map.lookup val res of
        Nothing ->
          Distinct (k' (Singleton x))
        Just tree ->
          aux k' ts tree

data Statistics =
  Statistics {
    -- Total number of terms in the decision tree
    stat_num_terms :: !Int,
    -- Total number of tests executed
    stat_num_tests :: !Int,
    -- Number of distinct test cases used
    stat_num_test_cases :: !Int }
  deriving (Eq, Show)

statistics:: DecisionTree testcase result term -> Statistics
statistics DecisionTree{dt_tree = Nothing} =
  Statistics 0 0 0
statistics DecisionTree{dt_tree = Just dt_tree, ..} =
  Statistics {
    stat_num_terms = x,
    stat_num_tests = y,
    stat_num_test_cases = length dt_test_cases }
  where
    (x, y) = stat dt_tree

    -- Returns (number of terms, number of tests)
    stat Singleton{} = (1, 0)
    -- To calculate the number of test cases, note that each term
    -- under res executed one test case on the way through this node.
    stat (TestCase res) =
      (sum (map fst ss), sum [ x + y | (x, y) <- ss ])
      where
        ss = map stat (Map.elems res)
