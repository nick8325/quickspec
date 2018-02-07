-- A pruner that uses twee.
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module QuickSpec.Pruning.Twee where

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
import QuickSpec.Pruning.EncodeTypes
import QuickSpec.Pruning.Background
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict hiding (State)
import Control.Monad.Trans
import Control.Monad.IO.Class

data Config =
  Config {
    cfg_max_term_size :: Int,
    cfg_max_cp_depth :: Int }

instance (Pretty f, PrettyTerm f, Ord f, Typeable f, Sized f, Arity f, EqualsBonus f, f ~ Tagged g) => Ordered (Extended f) where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn

newtype UntypedTweePrunerT f m a =
  UntypedTweePruner (ReaderT Twee.Config (StateT (State (Extended f)) m) a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (UntypedTweePrunerT f) where
  lift = UntypedTweePruner . lift . lift

runUntypedTwee :: Monad m => Config -> UntypedTweePrunerT f m a -> m a
runUntypedTwee Config{..} (UntypedTweePruner x) =
  evalStateT (runReaderT x config) initialState
  where
    config =
      defaultConfig {
        Twee.cfg_max_term_size = cfg_max_term_size,
        Twee.cfg_max_cp_depth = cfg_max_cp_depth }

instance (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, EqualsBonus f, f ~ Tagged g, Monad m) =>
  Pruner (Term f) (UntypedTweePrunerT f m) where
  normaliser = UntypedTweePruner $ do
    state <- lift get
    return (normaliseTwee state)

  add prop = UntypedTweePruner $ do
    config <- ask
    state <- lift get
    lift (put $! addTwee config prop state)

instance Tester testcase term m => Tester testcase term (UntypedTweePrunerT f m) where
  test = lift . test

normaliseTwee :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, EqualsBonus f, f ~ Tagged g) =>
  State (Extended f) -> Term f -> Term f
normaliseTwee state t =
  fromTwee $
    result (normaliseTerm state (simplifyTerm state (skolemise t)))

addTwee :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, EqualsBonus f, f ~ Tagged g) =>
  Twee.Config -> Prop (Term f) -> State (Extended f) -> State (Extended f)
addTwee config ([] :=>: t :=: u) state =
  completePure config $
    addAxiom config state axiom
  where
    axiom = Axiom 0 (prettyShow (t :=: u)) (toTwee t Twee.:=: toTwee u)

addTwee _ _ _ =
  error "twee pruner doesn't support non-unit equalities"

toTwee :: (Ord f, Typeable f) =>
  Term f -> Twee.Term (Extended f)
toTwee = Twee.build . tt
  where
    tt (Var (V _ x)) =
      Twee.var (Twee.V x)
    tt (App f ts) =
      Twee.app (Twee.fun (Function f)) (map tt ts)

skolemise :: (Ord f, Typeable f) =>
  Term f -> Twee.Term (Extended f)
skolemise = Twee.build . sk
  where
    sk (Var (V _ x)) =
      Twee.con (Twee.fun (Skolem (Twee.V x)))
    sk (App f ts) =
      Twee.app (Twee.fun (Function f)) (map sk ts)

fromTwee :: (Ord f, Typeable f) =>
  Twee.Term (Extended f) -> Term f
fromTwee = unsk
  where
    unsk (Twee.App (F Minimal) Empty) =
      Var (V typeVar 0)
    unsk (Twee.App (F (Skolem (Twee.V x))) Empty) =
      Var (V typeVar x)
    unsk (Twee.App (F (Function f)) ts) =
      App f (map unsk (unpack ts))

newtype TweePrunerT f m a =
  TweePruner (WithBackground f (MonoPruner f (UntypedTweePrunerT (Tagged f) m)) a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (TweePrunerT f) where
  lift = TweePruner . lift . lift . lift

runTwee :: (Background f, Monad m) => Config -> TweePrunerT f m a -> m a
runTwee config (TweePruner x) =
  runUntypedTwee config (runEncodeTypes (runWithBackground x))
instance (Ord f, Typed f, Background f, Typeable f, Arity f, Sized f, PrettyTerm f, Monad m) =>
  Pruner (Term f) (TweePrunerT f m) where
  normaliser = TweePruner normaliser
  add prop = TweePruner (add prop)

instance Tester testcase term m => Tester testcase term (TweePrunerT f m) where
  test = lift . test
