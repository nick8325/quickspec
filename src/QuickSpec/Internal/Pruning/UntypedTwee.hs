-- A pruner that uses twee. Does not respect types.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module QuickSpec.Internal.Pruning.UntypedTwee where

import QuickSpec.Internal.Testing
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import Data.Lens.Light
import qualified Twee
import qualified Twee.Equation as Twee
import qualified Twee.KBO as KBO
import qualified Twee.Base as Twee
import Twee hiding (Config(..))
import Twee.Rule hiding (normalForms)
import Twee.Proof hiding (Config, defaultConfig)
import Twee.Base(Ordered(..), Labelled)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict hiding (State)
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import QuickSpec.Internal.Terminal
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IntMap
import Control.Monad

data Config =
  Config {
    cfg_max_term_size :: Int,
    cfg_max_cp_depth :: Int }

lens_max_term_size = lens cfg_max_term_size (\x y -> y { cfg_max_term_size = x })
lens_max_cp_depth = lens cfg_max_cp_depth (\x y -> y { cfg_max_cp_depth = x })

data Extended fun = Minimal | Skolem Twee.Var | Function fun
  deriving (Eq, Ord, Typeable)

instance (Ord fun, Typeable fun) => Labelled (Extended fun)

instance Sized fun => Sized (Extended fun) where
  size (Function f) = size f
  size _ = 1

instance KBO.Sized (Extended fun) where
  size _ = 1

instance Arity fun => Arity (Extended fun) where
  arity (Function f) = arity f
  arity (Skolem _) = 0
  arity Minimal = 0

instance (Ord fun, Typeable fun) => Twee.Minimal (Extended fun) where
  minimal = Twee.fun Minimal

instance EqualsBonus (Extended fun)

instance (Ord fun, Typeable fun, Pretty fun) => Pretty (Extended fun) where
  pPrintPrec l p (Function f) = pPrintPrec l p f
  pPrintPrec _ _ Minimal = text "?"
  pPrintPrec _ _ (Skolem (Twee.V x)) = text ("sk" ++ show x)

instance (Ord fun, Typeable fun, PrettyTerm fun) => PrettyTerm (Extended fun) where
  termStyle (Function f) = termStyle f
  termStyle _ = curried

instance (Sized fun, Pretty fun, PrettyTerm fun, Ord fun, Typeable fun, Arity fun, EqualsBonus fun) => Ordered (Extended fun) where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn
  lessEqSkolem = KBO.lessEqSkolem

newtype Pruner fun m a =
  Pruner (ReaderT (Twee.Config (Extended fun)) (StateT (State (Extended fun)) m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift

run :: (Typeable fun, Ord fun, Sized fun, Monad m) => Config -> Pruner fun m a -> m a
run Config{..} (Pruner x) =
  evalStateT (runReaderT x config) (initialState config)
  where
    config =
      defaultConfig {
        Twee.cfg_accept_term = Just (\t -> size t <= cfg_max_term_size),
        Twee.cfg_max_cp_depth = cfg_max_cp_depth }

instance (Labelled fun, Sized fun) => Sized (Twee.Term fun) where
  size (Twee.Var _) = 1
  size (Twee.App f ts) =
    size (Twee.fun_value f) + sum (map size (Twee.unpack ts))

instance KBO.Weighted (Extended fun) where
  argWeight _ = 1

type Norm fun = Twee.Term (Extended fun)

instance (Ord fun, Typed fun, Typeable fun, Arity fun, PrettyTerm fun, EqualsBonus fun, Sized fun, Monad m) =>
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
    let (t' :=: u') = canonicalise (t :=: u)
    if not (null (Set.intersection (normalFormsTwee state t') (normalFormsTwee state u'))) then
      return False
    else do
      lift (put $! addTwee config t u state)
      return True

  add _ =
    return True
    --error "twee pruner doesn't support non-unit equalities"

  decodeNormalForm hole t = return (decode t (error "ambiguously-typed term"))
    where
      decode (Twee.Var (Twee.V n)) ty =
        Just (Var (V ty n))
      decode (Twee.App (Twee.F _ Minimal) Twee.Empty) ty =
        hole ty
      decode (Twee.App (Twee.F _ (Skolem (Twee.V n))) Twee.Empty) ty =
        Just (Var (V ty n))
      decode (Twee.App (Twee.F _ (Function f)) ts) ty =
        (Fun f :@:) <$> zipWithM decode (Twee.unpack ts) args
        where
          args = typeArgs (typ f)

  normTheorems = Pruner $ do
    state <- lift get
    let actives = IntMap.elems (Twee.st_active_set state)
    let
      toTheorem active =
        Theorem
          (toProp (equation proof))
          (map toAxiom . Map.toList . groundAxiomsAndSubsts $ deriv)
        where
          proof = Twee.active_proof active
          deriv = derivation proof
          toProp (t Twee.:=: u) = [] :=>: t :=: u
          toAxiom (ax, subs) = (toProp eqn, map toProp [Twee.subst sub eqn | sub <- Set.toList subs])
            where
              eqn = axiom_eqn ax

    return (map toTheorem actives)

normaliseTwee :: (Ord fun, Typeable fun, Arity fun, PrettyTerm fun, EqualsBonus fun, Sized fun) =>
  State (Extended fun) -> Term fun -> Norm fun
normaliseTwee state t =
  result u (normaliseTerm state u)
  where
    u = simplifyTerm state (skolemise t)

normalFormsTwee :: (Ord fun, Typeable fun, Arity fun, PrettyTerm fun, EqualsBonus fun, Sized fun) =>
  State (Extended fun) -> Term fun -> Set (Norm fun)
normalFormsTwee state t =
  Set.fromList . Map.elems $ Map.mapWithKey result (normalForms state (skolemise t))

addTwee :: (Ord fun, Typeable fun, Arity fun, PrettyTerm fun, EqualsBonus fun, Sized fun) =>
  Twee.Config (Extended fun) -> Term fun -> Term fun -> State (Extended fun) -> State (Extended fun)
addTwee config t u state =
  interreduce config $
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
    tt (Fun f :@: ts) =
      Twee.app (Twee.fun (Function f)) (map tt ts)
    tt _ = error "partially applied term"

skolemise :: (Ord f, Typeable f) =>
  Term f -> Twee.Term (Extended f)
skolemise = Twee.build . sk
  where
    sk (Var (V _ x)) =
      Twee.con (Twee.fun (Skolem (Twee.V x)))
    sk (Fun f :@: ts) =
      Twee.app (Twee.fun (Function f)) (map sk ts)
    sk _ = error "partially applied term"
