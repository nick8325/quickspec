-- A pruner that uses twee. Supports types and background axioms.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module QuickSpec.Internal.Pruning.Twee(Config(..), module QuickSpec.Internal.Pruning.Twee) where

import QuickSpec.Internal.Testing
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Term
import QuickSpec.Internal.Terminal
import qualified QuickSpec.Internal.Pruning.Types as Types
import qualified QuickSpec.Internal.Pruning.Background as Background
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import qualified QuickSpec.Internal.Pruning.UntypedTwee as Untyped
import QuickSpec.Internal.Pruning.UntypedTwee(Config(..))

newtype Pruner fun m a =
  Pruner (Types.Pruner fun (Background.Pruner (Types.Tagged fun) (Untyped.Pruner (Types.Tagged fun) m)) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term,
            MonadPruner (Term fun) (Untyped.Norm (Types.Tagged fun)), MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift . lift

run :: (Sized fun, Monad m) => Config -> Pruner fun m a -> m a
run config (Pruner x) =
  Untyped.run config (Background.run (Types.run x))
