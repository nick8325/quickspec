-- A pruner that uses twee. Supports types and background axioms.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module QuickSpec.Pruning.Twee(Config(..), module QuickSpec.Pruning.Twee) where

import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Terminal
import qualified QuickSpec.Pruning.Types as Types
import qualified QuickSpec.Pruning.Background as Background
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import qualified QuickSpec.Pruning.UntypedTwee as Untyped
import QuickSpec.Pruning.UntypedTwee(Config(..))

newtype Pruner fun m a =
  Pruner (Types.Pruner fun (Background.Pruner (Types.Tagged fun) (Untyped.Pruner (Types.Tagged fun) m)) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term,
            MonadPruner (Term fun) (Untyped.Norm (Types.Tagged fun)), MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift . lift

run :: (Sized fun, Monad m) => Config -> Pruner fun m a -> m a
run config (Pruner x) =
  Untyped.run config (Background.run (Types.run x))
