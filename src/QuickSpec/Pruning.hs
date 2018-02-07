-- A type of pruners.
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module QuickSpec.Pruning where

import QuickSpec.Prop

class Monad m => Pruner term m | m -> term where
  normaliser :: m (term -> term)
  add :: Prop term -> m ()

normalise :: Pruner term m => term -> m term
normalise t = do
  norm <- normaliser
  return (norm t)
