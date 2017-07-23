-- Testing conjectures using QuickCheck.
{-# LANGUAGE FlexibleContexts, RecordWildCards, TupleSections #-}
module QuickSpec.Testing.QuickCheck where

import QuickSpec.Testing
import QuickSpec.Prop
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Control.Monad
import Data.List
import System.Random

data Config =
  Config {
    cfg_num_tests :: Int,
    cfg_max_test_size :: Int }
  deriving Show

quickCheckTester :: Eq result =>
  Config -> Gen testcase -> (testcase -> term -> result) ->
  Gen (Tester testcase term)
quickCheckTester config gen eval =
  makeTester <$> quickCheckTest config gen eval <$> arbitrary

quickCheckTest :: Eq result => 
  Config -> Gen testcase -> (testcase -> term -> result) -> QCGen ->
  Prop term -> Maybe testcase
quickCheckTest Config{..} gen eval seed =
  \(lhs :=>: rhs) ->
    let
      test testcase = do
        guard $
          all (testEq testcase) lhs &&
          not (testEq testcase rhs)
        return testcase
    in
    msum (map test tests)
  where
    seeds = unfoldr (Just . split) seed
    sizes = cycle [0, 2..cfg_max_test_size]
    tests = take cfg_num_tests (zipWith (unGen gen) seeds sizes)

    testEq testcase (t :=: u) =
      eval testcase t == eval testcase u
