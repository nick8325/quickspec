-- A pruner that uses twee.
{-# LANGUAGE RecordWildCards, FlexibleContexts #-}
module QuickSpec.Pruning.Twee where

import QuickSpec.Pruning
import QuickSpec.Prop
import Data.Typeable
import qualified Twee
import Twee hiding (Config(..))
import qualified Twee.Rule as Twee
import qualified Twee.Equation as Twee
import Twee.Proof hiding (Config(..))
import Twee.Base

data Config =
  Config {
    cfg_max_term_size :: Int,
    cfg_max_cp_depth :: Int }

tweePruner :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, Ordered (Extended f)) =>
  Config -> Pruner (Term f)
tweePruner Config{..} =
  makePruner normaliseTwee (addTwee config) Twee.initialState
  where
    config =
      Twee.defaultConfig {
        Twee.cfg_max_term_size = cfg_max_term_size,
        Twee.cfg_max_cp_depth = cfg_max_cp_depth }

normaliseTwee :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, Ordered (Extended f)) =>
  State (Extended f) -> Term f -> Term f
normaliseTwee state t =
  unskolemise $
    Twee.result (Twee.normaliseTerm state (Twee.simplifyTerm state (skolemise t)))

addTwee :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, Ordered (Extended f)) =>
  Twee.Config -> Prop (Term f) -> State (Extended f) -> State (Extended f)
addTwee config ([] :=>: t :=: u) state =
  completePure config $
    addAxiom config state axiom
  where
    axiom = Axiom 0 (prettyShow (t :=: u)) (extend t Twee.:=: extend u)
    extend = build . mapFun (fun . Function . fun_value)

addTwee _ _ _ =
  error "twee pruner doesn't support non-unit equalities"

skolemise :: (Ord f, Typeable f) =>
  Term f -> Term (Extended f)
skolemise = build . sk
  where
    sk (Var x) =
      con (fun (Skolem x))
    sk (App (F f) ts) =
      app (fun (Function f)) (map sk (unpack ts))

unskolemise :: (Ord f, Typeable f) =>
  Term (Extended f) -> Term f
unskolemise = build . unsk
  where
    unsk (App (F Minimal) Empty) =
      var (V 0)
    unsk (App (F (Skolem x)) Empty) =
      var x
    unsk (App (F (Function f)) ts) =
      app (fun f) (map unsk (unpack ts))
