-- A pruner that uses twee.
{-# LANGUAGE RecordWildCards, FlexibleContexts #-}
module QuickSpec.Pruning.Twee where

import QuickSpec.Pruning
import QuickSpec.Prop
import Data.Typeable
import qualified Twee
import Twee hiding (Config(..), State(..))
import qualified Twee.Rule as Twee
import qualified Twee.Equation as Twee
import Twee.Proof hiding (Config(..))
import Twee.Base

data Config =
  Config {
    cfg_max_term_size :: Int }

data State f =
  State {
    st_config :: Twee.Config,
    st_state  :: Twee.State (Extended f) }

tweePruner :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, Ordered (Extended f)) =>
  Config -> Pruner (Term f)
tweePruner Config{..} =
  makePruner normaliseTwee addTwee
    State {
      st_config =
        Twee.defaultConfig {
          Twee.cfg_max_term_size = cfg_max_term_size },
      st_state = Twee.initialState }

normaliseTwee :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, Ordered (Extended f)) =>
  State f -> Term f -> Term f
normaliseTwee State{..} t =
  unskolemise $
    Twee.result (Twee.normaliseTerm st_state (skolemise t))

addTwee :: (Ord f, Typeable f, Arity f, Sized f, PrettyTerm f, Ordered (Extended f)) =>
  Prop (Term f) -> State f -> State f
addTwee ([] :=>: t :=: u) st@State{..} =
  st {
    st_state =
      completePure st_config $
        addAxiom st_config st_state axiom }
  where
    axiom =
      Axiom 0 (prettyShow (t :=: u))
        (skolemise t Twee.:=: skolemise u)
      
addTwee _ _ =
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
