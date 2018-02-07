-- Testing conjectures using QuickCheck.
{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module QuickSpec.Testing.QuickCheck where

import QuickSpec.Testing
import QuickSpec.Prop
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Data.List
import System.Random

data Config =
  Config {
    cfg_num_tests :: Int,
    cfg_max_test_size :: Int }
  deriving Show

data QuickCheckTesterStuff testcase term result =
  QuickCheckTesterStuff {
    qc_config :: Config,
    qc_gen :: Gen testcase,
    qc_eval :: testcase -> term -> result,
    qc_seed :: QCGen }

newtype QuickCheckTester testcase term result m a =
  QuickCheckTester (ReaderT (QuickCheckTesterStuff testcase term result) m a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (QuickCheckTester testcase term result) where
  lift = QuickCheckTester . lift

runQuickCheckTester ::
  Config -> Gen testcase -> (testcase -> term -> result) ->
  QuickCheckTester testcase term result m a -> Gen (m a)
runQuickCheckTester config gen eval (QuickCheckTester x) = do
  seed <- arbitrary
  return (runReaderT x (QuickCheckTesterStuff config gen eval seed))

instance (Monad m, Eq result) => Tester testcase term (QuickCheckTester testcase term result m) where
  test prop =
    QuickCheckTester $ do
      stuff <- ask
      return (quickCheckTest stuff prop)

quickCheckTest :: Eq result => 
  QuickCheckTesterStuff testcase term result ->
  Prop term -> Maybe testcase
quickCheckTest QuickCheckTesterStuff{qc_config = Config{..}, ..} =
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
    seeds = unfoldr (Just . split) qc_seed
    sizes = cycle [0, 2..cfg_max_test_size]
    tests = take cfg_num_tests (zipWith (unGen qc_gen) seeds sizes)

    testEq testcase (t :=: u) =
      qc_eval testcase t == qc_eval testcase u
