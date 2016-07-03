-- A typeclass for pruners.
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module QuickSpec.Pruner where

import QuickSpec.Term
import QuickSpec.Prop

class Pruner f a | a -> f where
  normalise :: a -> Term f -> Term f
  add :: Prop (Term f) -> a -> a
