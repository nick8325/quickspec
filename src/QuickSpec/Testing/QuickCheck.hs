-- Testing conjectures using QuickCheck.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, MultiParamTypeClasses, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module QuickSpec.Testing.QuickCheck where

import QuickSpec.Testing
import QuickSpec.Pruning
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
import QuickSpec.Terminal
import QuickSpec.Utils

data Config =
  Config {
    cfg_num_tests :: Int,
    cfg_max_test_size :: Int,
    cfg_fixed_seed :: Maybe QCGen}
  deriving Show

makeLensAs ''Config
  [("cfg_num_tests", "lens_num_tests"),
   ("cfg_max_test_size", "lens_max_test_size"),
   ("cfg_fixed_seed", "lens_fixed_seed")]

data Environment testcase term result =
  Environment {
    env_config :: Config,
    env_tests :: [testcase],
    env_eval :: testcase -> term -> result }

newtype Tester testcase term result m a =
  Tester (ReaderT (Environment testcase term result) m a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTerminal, MonadPruner term' res')

instance MonadTrans (Tester testcase term result) where
  lift = Tester . lift

run ::
  Config -> Gen testcase -> (testcase -> term -> result) ->
  Tester testcase term result m a -> Gen (m a)
run config@Config{..} gen eval (Tester x) = do
  seed <- maybe arbitrary return cfg_fixed_seed
  let
    seeds = unfoldr (Just . split) seed
    n = cfg_num_tests
    k = max 1 cfg_max_test_size
    bias = 3
    -- Bias tests towards smaller sizes.
    -- We do this by distributing the cube of the size uniformly.
    sizes =
      reverse $ map (k -) $
      map (truncate . (** (1/fromInteger bias)) . fromIntegral) $
      uniform (toInteger n) (toInteger k^bias)
    tests = zipWith (unGen gen) seeds sizes
  return $ runReaderT x
    Environment {
      env_config = config,
      env_tests = tests,
      env_eval = eval }

-- uniform n k: generate a list of n integers which are distributed evenly between 0 and k-1.
uniform :: Integer -> Integer -> [Integer]
uniform n k =
  -- n `div` k: divide evenly as far as possible.
  concat [replicate (fromIntegral (n `div` k)) i | i <- [0..k-1]] ++
  -- The leftovers get distributed at equal intervals.
  [i * k `div` leftovers | i <- [0..leftovers-1]]
  where
    leftovers = n `mod` k

instance (Monad m, Eq result) => MonadTester testcase term (Tester testcase term result m) where
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
