-- A type of pruners.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances, DefaultSignatures, GADTs #-}
module QuickSpec.Internal.Pruning where


import QuickSpec.Internal.Type (Arity (..))  
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Testing
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader

class Monad m => MonadPruner term norm m | m -> term norm where
  normaliser :: m (term -> norm)
  add :: Prop term -> m Bool

  default normaliser :: (MonadTrans t, MonadPruner term norm m', m ~ t m') => m (term -> norm)
  normaliser = lift normaliser

  default add :: (MonadTrans t, MonadPruner term norm m', m ~ t m') => Prop term -> m Bool
  add = lift . add

instance MonadPruner term norm m => MonadPruner term norm (StateT s m)
instance MonadPruner term norm m => MonadPruner term norm (ReaderT r m)

normalise :: MonadPruner term norm m => term -> m norm
normalise t = do
  norm <- normaliser
  return (norm t)

newtype ReadOnlyPruner m a = ReadOnlyPruner { withReadOnlyPruner :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term)

instance MonadTrans ReadOnlyPruner where
  lift = ReadOnlyPruner

instance MonadPruner term norm m => MonadPruner term norm (ReadOnlyPruner m) where
  normaliser = ReadOnlyPruner normaliser
  add _ = return True

newtype WatchPruner term m a = WatchPruner (StateT [Prop term] m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadTester testcase term)

instance MonadPruner term norm m => MonadPruner term norm (WatchPruner term m) where
  normaliser = lift normaliser
  add prop = do
    res <- lift (add prop)
    WatchPruner (modify (prop:))
    return res

watchPruner :: Monad m => WatchPruner term m a -> m (a, [Prop term])
watchPruner (WatchPruner mx) = do
  (x, props) <- runStateT mx []
  return (x, reverse props)
    
