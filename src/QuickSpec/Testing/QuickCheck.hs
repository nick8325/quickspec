-- Testing conjectures using QuickCheck.
{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, MultiParamTypeClasses, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module QuickSpec.Testing.QuickCheck where

import QuickSpec.Testing
import QuickSpec.Prop
import Test.QuickCheck
import Test.QuickCheck.Gen
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.List
import System.Random
import QuickSpec.Terminal
import QuickSpec.Utils

data Config =
  Config {
    cfg_num_tests :: Int,
    cfg_max_test_size :: Int }
  deriving Show

makeLensAs ''Config
  [("cfg_num_tests", "lens_num_tests"),
   ("cfg_max_test_size", "lens_max_test_size")]

data Environment testcase term result =
  Environment {
    env_config :: Config,
    env_tests :: [testcase],
    env_eval :: testcase -> term -> result }

newtype Tester testcase term result m a =
  Tester (ReaderT (Environment testcase term result) m a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTerminal)

instance MonadTrans (Tester testcase term result) where
  lift = Tester . lift

run ::
  Config -> Gen testcase -> (testcase -> term -> result) ->
  Tester testcase term result m a -> Gen (m a)
run config@Config{..} gen eval (Tester x) = do
  seed <- arbitrary
  let
    seeds = unfoldr (Just . split) seed
    n = cfg_num_tests
    k = cfg_max_test_size
    -- Divide tests equally between all sizes.
    -- There are n total tests of k+1 different sizes.
    -- If it doesn't divide equally, the biggest size gets the
    -- left-overs.
    sizes =
      concat [replicate (n `div` (k+1)) i | i <- [0..k-1]] ++
      replicate (n `divRoundUp` (k+1)) k
    m `divRoundUp` n = (m-1) `div` n + 1
    tests = zipWith (unGen gen) seeds sizes
  return $ runReaderT x
    Environment {
      env_config = config,
      env_tests = tests,
      env_eval = eval }

instance (MonadTerminal m, Eq result) => MonadTester testcase term (Tester testcase term result m) where
  test prop =
    Tester $ do
      env <- ask
      return $! quickCheckTest env prop

quickCheckTest :: Eq result =>
  Environment testcase term result ->
  Prop term -> Maybe testcase
quickCheckTest Environment{env_config = Config{..}, ..} (lhs :=>: rhs) =
  msum (map test env_tests)
  where
    test testcase = do
        guard $
          all (testEq testcase) lhs &&
          not (testEq testcase rhs)
        return testcase

    testEq testcase (t :=: u) =
      env_eval testcase t == env_eval testcase u
