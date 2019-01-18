-- A pruner that uses twee. Supports types and background axioms.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module QuickSpec.Internal.Pruning.Twee(Config(..), module QuickSpec.Internal.Pruning.Twee) where

import QuickSpec.Internal.Testing
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Term
import QuickSpec.Internal.Terminal
import qualified QuickSpec.Internal.Pruning.Types as Types
import QuickSpec.Internal.Pruning.Types(Tagged)
import qualified QuickSpec.Internal.Pruning.PartialApplication as PartialApplication
import QuickSpec.Internal.Pruning.PartialApplication(PartiallyApplied)
import qualified QuickSpec.Internal.Pruning.Background as Background
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import qualified QuickSpec.Internal.Pruning.UntypedTwee as Untyped
import QuickSpec.Internal.Pruning.UntypedTwee(Config(..))

newtype Pruner fun m a =
  Pruner (PartialApplication.Pruner fun (Types.Pruner (PartiallyApplied fun) (Background.Pruner (Tagged (PartiallyApplied fun)) (Untyped.Pruner (Tagged (PartiallyApplied fun)) m))) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term,
            MonadPruner (Term fun) (Untyped.Norm (Tagged (PartiallyApplied fun))), MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift . lift . lift

run :: (Sized fun, Monad m) => Config -> Pruner fun m a -> m a
run config (Pruner x) =
  Untyped.run config (Background.run (Types.run (PartialApplication.run x)))
