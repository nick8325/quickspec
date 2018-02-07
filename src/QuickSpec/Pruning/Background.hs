-- A pruning layer which automatically adds axioms about functions as they appear.
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, GeneralizedNewtypeDeriving, UndecidableInstances, TypeOperators #-}
module QuickSpec.Pruning.Background where

import QuickSpec.Term
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Prop
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict hiding (State)

newtype WithBackground f m a =
  WithBackground (StateT (Set f) m a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (WithBackground f) where
  lift = WithBackground . lift

class Background f where
  background :: f -> [Prop (Term f)]
  background _ = []

runWithBackground :: (Monad m, Background f) => WithBackground f m a -> m a
runWithBackground (WithBackground x) =
  evalStateT x Set.empty

instance (Ord f, Background f, Pruner (Term f) m) =>
  Pruner (Term f) (WithBackground f m) where
  normaliser = lift normaliser
  add prop = do
    mapM_ addFunction (funs prop)
    lift (add prop)

instance Tester testcase term m => Tester testcase term (WithBackground f m) where
  test = lift . test

addFunction :: (Ord f, Background f, Pruner (Term f) m) => f -> WithBackground f m ()
addFunction f = do
  funcs <- WithBackground get
  unless (f `Set.member` funcs) $ do
    WithBackground (put (Set.insert f funcs))
    mapM_ add (background f)

instance (Background fun1, Background fun2) => Background (fun1 :+: fun2) where
  background (Inl x) = map (fmap (fmap Inl)) (background x)
  background (Inr x) = map (fmap (fmap Inr)) (background x)
