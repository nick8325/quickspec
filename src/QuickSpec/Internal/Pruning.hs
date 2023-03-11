-- A type of pruners.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances, DefaultSignatures, GADTs, DeriveFunctor, DeriveTraversable #-}
module QuickSpec.Internal.Pruning where

import QuickSpec.Internal.Type (Type, Arity (..))  
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Testing
import Twee.Pretty
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader

data Theorem norm =
  Theorem {
    prop :: Prop norm,
    axiomsUsed :: [(Prop norm, [Prop norm])] }
  deriving (Functor, Foldable, Traversable)

instance Pretty norm => Pretty (Theorem norm) where
  pPrint thm =
    (text "prop =" <+> pPrint (prop thm)) $$
    (text "axioms used =" <+> pPrint (axiomsUsed thm))

class Monad m => MonadPruner term norm m | m -> term norm where
  normaliser :: m (term -> norm)
  add :: Prop term -> m Bool
  decodeNormalForm :: (Type -> term) -> norm -> m term
  normTheorems :: m [Theorem norm]

  default normaliser :: (MonadTrans t, MonadPruner term norm m', m ~ t m') => m (term -> norm)
  normaliser = lift normaliser

  default add :: (MonadTrans t, MonadPruner term norm m', m ~ t m') => Prop term -> m Bool
  add = lift . add

  default normTheorems :: (MonadTrans t, MonadPruner term' norm m', m ~ t m') => m [Theorem norm]
  normTheorems = lift normTheorems

  default decodeNormalForm :: (MonadTrans t, MonadPruner term norm m', m ~ t m') => (Type -> term) -> norm -> m term
  decodeNormalForm hole t = lift (decodeNormalForm hole t)

theorems :: MonadPruner term norm m => (Type -> term) -> m [Theorem term]
theorems hole = do
  thms <- normTheorems
  mapM (mapM (decodeNormalForm hole)) thms

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
    
