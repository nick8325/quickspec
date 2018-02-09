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
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.List
import System.Random

data Config =
  Config {
    cfg_num_tests :: Int,
    cfg_max_test_size :: Int }
  deriving Show

data Environment testcase term result =
  Environment {
    env_config :: Config,
    env_gen :: Gen testcase,
    env_eval :: testcase -> term -> result,
    env_seed :: QCGen }

newtype Tester testcase term result m a =
  Tester (ReaderT (Environment testcase term result) m a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (Tester testcase term result) where
  lift = Tester . lift

run ::
  Config -> Gen testcase -> (testcase -> term -> result) ->
  Tester testcase term result m a -> Gen (m a)
run config gen eval (Tester x) = do
  seed <- arbitrary
  return $ runReaderT x
    Environment {
      env_config = config,
      env_gen = gen,
      env_eval = eval,
      env_seed = seed }

instance (Monad m, Eq result) => MonadTester testcase term (Tester testcase term result m) where
  test prop =
    Tester $ do
      env <- ask
      return (quickCheckTest env prop)

quickCheckTest :: Eq result => 
  Environment testcase term result ->
  Prop term -> Maybe testcase
quickCheckTest Environment{env_config = Config{..}, ..} =
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
    seeds = unfoldr (Just . split) env_seed
    sizes = cycle [0, 2..cfg_max_test_size]
    tests = take cfg_num_tests (zipWith (unGen env_gen) seeds sizes)

    testEq testcase (t :=: u) =
      env_eval testcase t == env_eval testcase u
