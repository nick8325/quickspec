-- A type of test case generators.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FunctionalDependencies, DefaultSignatures, GADTs, FlexibleInstances, UndecidableInstances, TypeOperators, DeriveFunctor #-}
module QuickSpec.Internal.Testing where

import QuickSpec.Internal.Prop
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader

data TestResult testcase =
    TestPassed
  | TestFailed testcase
  | Untestable
  deriving (Functor, Eq)

testResult :: TestResult testcase -> TestResult ()
testResult = fmap (const ())

testAnd :: TestResult testcase -> TestResult testcase -> TestResult testcase
TestPassed `testAnd` x = x
x `testAnd` _ = x

testImplies :: TestResult testcase -> TestResult testcase -> TestResult testcase
TestPassed `testImplies` x = x
TestFailed _ `testImplies` _ = TestPassed
Untestable `testImplies` _ = Untestable

class Monad m => MonadTester testcase term m | m -> testcase term where
  test :: Prop term -> m (TestResult testcase)
  retest :: testcase -> Prop term -> m (TestResult testcase)

  default test :: (MonadTrans t, MonadTester testcase term m', m ~ t m') => Prop term -> m (TestResult testcase)
  test = lift . test

  default retest :: (MonadTrans t, MonadTester testcase term m', m ~ t m') => testcase -> Prop term -> m (TestResult testcase)
  retest tc = lift . retest tc

instance MonadTester testcase term m => MonadTester testcase term (StateT s m)
instance MonadTester testcase term m => MonadTester testcase term (ReaderT r m)
