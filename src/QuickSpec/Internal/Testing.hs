-- A type of test case generators.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DefaultSignatures, GADTs, FlexibleInstances, UndecidableInstances #-}
module QuickSpec.Internal.Testing where

import QuickSpec.Internal.Prop
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader

data TestResult testcase =
    TestPassed
  | TestFailed testcase

class Monad m => MonadTester testcase term m | m -> testcase term where
  test :: Prop term -> m (Maybe (TestResult testcase))

  default test :: (MonadTrans t, MonadTester testcase term m', m ~ t m') => Prop term -> m (Maybe (TestResult testcase))
  test = lift . test

instance MonadTester testcase term m => MonadTester testcase term (StateT s m)
instance MonadTester testcase term m => MonadTester testcase term (ReaderT r m)
