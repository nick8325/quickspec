-- A pruner that uses twee.
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module QuickSpec.Pruning.Twee(Config(..), module QuickSpec.Pruning.Twee) where

import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Type
import Data.Typeable
import qualified Twee
import qualified Twee.Equation as Twee
import qualified Twee.KBO as KBO
import qualified Twee.Base as Twee
import Twee hiding (Config(..))
import Twee.Rule
import Twee.Proof hiding (Config, defaultConfig)
import Twee.Base(Ordered(..), Extended(..), EqualsBonus, pattern F, pattern Empty, unpack)
import qualified QuickSpec.Pruning.Types as Types
import qualified QuickSpec.Pruning.Background as Background
import QuickSpec.Pruning.Background(Background)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict hiding (State)
import Control.Monad.Trans
import Control.Monad.IO.Class
import qualified QuickSpec.Pruning.UntypedTwee as Untyped
import QuickSpec.Pruning.UntypedTwee(Config(..))

newtype Pruner fun m a =
  Pruner (Background.Pruner fun (Types.Pruner fun (Untyped.Pruner (Types.Tagged fun) m)) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadPruner (Term fun))

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift . lift

run :: (Background fun, Monad m) => Config -> Pruner fun m a -> m a
run config (Pruner x) =
  Untyped.run config (Types.run (Background.run x))
