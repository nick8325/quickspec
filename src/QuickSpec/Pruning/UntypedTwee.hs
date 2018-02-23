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
import Twee.Base(Ordered(..), Extended(..), EqualsBonus, pattern F, pattern Empty, unpack)
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

instance (Pretty fun, PrettyTerm fun, Ord fun, Typeable fun, Sized fun, Arity fun, EqualsBonus fun) => Ordered (Extended fun) where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn

newtype Pruner fun m a =
  Pruner (ReaderT Twee.Config (StateT (State (Extended fun)) m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift

run :: Monad m => Config -> Pruner fun m a -> m a
run Config{..} (Pruner x) =
  evalStateT (runReaderT x config) initialState
  where
    config =
      defaultConfig {
        Twee.cfg_max_term_size = cfg_max_term_size,
        Twee.cfg_max_cp_depth = cfg_max_cp_depth }

instance (Ord fun, Typeable fun, Arity fun, Sized fun, PrettyTerm fun, EqualsBonus fun, Monad m) =>
  MonadPruner (Term fun) (Term fun) (Pruner fun m) where
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

normaliseTwee :: (Ord fun, Typeable fun, Arity fun, Sized fun, PrettyTerm fun, EqualsBonus fun) =>
  State (Extended fun) -> Term fun -> Term fun
normaliseTwee state t =
  fromTwee $
    result (normaliseTerm state (simplifyTerm state (skolemise t)))

normalFormsTwee :: (Ord fun, Typeable fun, Arity fun, Sized fun, PrettyTerm fun, EqualsBonus fun) =>
  State (Extended fun) -> Term fun -> Set (Term fun)
normalFormsTwee state t =
  Set.map fromTwee $
    Set.map result (normalForms state (skolemise t))

addTwee :: (Ord fun, Typeable fun, Arity fun, Sized fun, PrettyTerm fun, EqualsBonus fun) =>
  Twee.Config -> Term fun -> Term fun -> State (Extended fun) -> State (Extended fun)
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

fromTwee :: Twee.Term (Extended f) -> Term f
fromTwee = unsk
  where
    unsk (Twee.App (F Minimal) Empty) =
      Var (V typeVar 0)
    unsk (Twee.App (F (Skolem (Twee.V x))) Empty) =
      Var (V typeVar x)
    unsk (Twee.App (F (Function f)) ts) =
      App f (map unsk (unpack ts))
    unsk _ = error "variable introduced by rewriting"
