-- A type of pruners.
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances, DefaultSignatures, GADTs #-}
module QuickSpec.Pruning where

import QuickSpec.Prop
import QuickSpec.Testing
import Control.Monad.Trans
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader

class Monad m => MonadPruner term m | m -> term where
  normaliser :: m (term -> term)
  add :: Prop term -> m ()

  default normaliser :: (MonadTrans t, MonadPruner term m', m ~ t m') => m (term -> term)
  normaliser = lift normaliser

  default add :: (MonadTrans t, MonadPruner term m', m ~ t m') => Prop term -> m ()
  add = lift . add

instance MonadPruner term m => MonadPruner term (StateT s m)
instance MonadPruner term m => MonadPruner term (ReaderT r m)

normalise :: MonadPruner term m => term -> m term
normalise t = do
  norm <- normaliser
  return (norm t)


newtype ReadOnlyPruner m a = ReadOnlyPruner { withReadOnlyPruner :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term)

instance MonadTrans ReadOnlyPruner where
  lift = ReadOnlyPruner

instance MonadPruner term m => MonadPruner term (ReadOnlyPruner m) where
  normaliser = ReadOnlyPruner normaliser
  add _ = return ()

newtype WatchPruner term m a = WatchPruner (StateT [Prop term] m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadTester testcase term)

instance MonadPruner term m => MonadPruner term (WatchPruner term m) where
  normaliser = lift normaliser
  add prop = do
    WatchPruner (modify (prop:))
    lift (add prop)

watchPruner :: Monad m => WatchPruner term m a -> m (a, [Prop term])
watchPruner (WatchPruner mx) = do
  (x, props) <- runStateT mx []
  return (x, reverse props)
    
