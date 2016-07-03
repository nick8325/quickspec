-- A typeclass for running tests.
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module QuickSpec.Tester where

import QuickSpec.Term
import QuickSpec.Prop

class Tester f a | a -> f where
  testTerm :: Term f -> a -> Result f a

data Result f a = EqualTo (Term f) | Distinct a
