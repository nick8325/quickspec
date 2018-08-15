-- A pruner that uses twee. Does not respect types.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances, TemplateHaskell #-}
module QuickSpec.Pruning.UntypedTwee where

import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import qualified Twee
import qualified Twee.Equation as Twee
import qualified Twee.KBO as KBO
import qualified Twee.Base as Twee
import Twee hiding (Config(..))
import Twee.Rule hiding (normalForms)
import Twee.Proof hiding (Config, defaultConfig)
import Twee.Base(Ordered(..), Extended(..), EqualsBonus)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict hiding (State)
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import QuickSpec.Terminal
import qualified Data.Set as Set
import Data.Set(Set)

data Config =
  Config {
    cfg_max_term_size :: Int,
    cfg_max_cp_depth :: Int }

makeLensAs ''Config
  [("cfg_max_term_size", "lens_max_term_size"),
   ("cfg_max_cp_depth", "lens_max_cp_depth")]

instance (Pretty fun, PrettyTerm fun, Ord fun, Typeable fun, Twee.Sized fun, Arity fun, EqualsBonus fun) => Ordered (Extended fun) where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn

newtype Pruner fun m a =
  Pruner (ReaderT (Twee.Config (Extended fun)) (StateT (State (Extended fun)) m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift

run :: (Sized fun, Monad m) => Config -> Pruner fun m a -> m a
run Config{..} (Pruner x) =
  evalStateT (runReaderT x config) initialState
  where
    config =
      defaultConfig {
        Twee.cfg_accept_term = Just (\t -> size t <= cfg_max_term_size),
        Twee.cfg_max_cp_depth = cfg_max_cp_depth }

instance Sized fun => Sized (Twee.Term fun) where
  size (Twee.Var _) = 1
  size (Twee.App f ts) =
    size (Twee.fun_value f) + sum (map size (Twee.unpack ts))

instance Sized fun => Sized (Twee.Extended fun) where
  size Twee.Minimal = 1
  size (Twee.Skolem _) = 1
  size (Twee.Function f) = size f

type Norm fun = Twee.Term (Extended fun)

instance (Ord fun, Typeable fun, Arity fun, Twee.Sized fun, PrettyTerm fun, EqualsBonus fun, Monad m) =>
  MonadPruner (Term fun) (Norm fun) (Pruner fun m) where
  normaliser = Pruner $ do
    state <- lift get
    return $ \t ->
      let u = normaliseTwee state t in
      u
      -- traceShow (text "normalise:" <+> pPrint t <+> text "->" <+> pPrint u) u

  add ([] :=>: t :=: u) = Pruner $ do
    state <- lift get
    config <- ask
    let
      t' = normalFormsTwee state t
      u' = normalFormsTwee state u
    -- Add the property anyway in case it could only be joined
    -- by considering all normal forms
    lift (put $! addTwee config t u state)
    return (Set.null (Set.intersection t' u'))

  add _ =
    error "twee pruner doesn't support non-unit equalities"

normaliseTwee :: (Ord fun, Typeable fun, Arity fun, Twee.Sized fun, PrettyTerm fun, EqualsBonus fun) =>
  State (Extended fun) -> Term fun -> Norm fun
normaliseTwee state t =
  result (normaliseTerm state (simplifyTerm state (skolemise t)))

normalFormsTwee :: (Ord fun, Typeable fun, Arity fun, Twee.Sized fun, PrettyTerm fun, EqualsBonus fun) =>
  State (Extended fun) -> Term fun -> Set (Norm fun)
normalFormsTwee state t =
  Set.map result (normalForms state (skolemise t))

addTwee :: (Ord fun, Typeable fun, Arity fun, Twee.Sized fun, PrettyTerm fun, EqualsBonus fun) =>
  Twee.Config (Extended fun) -> Term fun -> Term fun -> State (Extended fun) -> State (Extended fun)
addTwee config t u state =
  completePure config $
    addAxiom config state axiom
  where
    axiom = Axiom 0 (prettyShow (t :=: u)) (toTwee t Twee.:=: toTwee u)

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
