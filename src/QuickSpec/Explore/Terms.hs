-- Theory exploration which accepts one term at a time.
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards, TemplateHaskell #-}
module QuickSpec.Explore.Terms where

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import QuickSpec.Prop
import QuickSpec.Type
import QuickSpec.Pruning
import QuickSpec.Testing
import QuickSpec.Testing.DecisionTree hiding (Result, Singleton)
import Control.Monad.Trans.State.Strict hiding (State)
import Data.Lens.Light
import QuickSpec.Utils

data Terms testcase result term =
  Terms {
    -- Empty decision tree.
    tm_empty :: DecisionTree testcase result term,
    -- Terms already explored. These are stored in the *values* of the map.
    -- The keys are those terms but normalised.
    -- We do it like this so that explore can guarantee to always return
    -- the same representative for each equivalence class (see below).
    tm_terms  :: Map term term,
    -- Decision tree mapping test case results to terms.
    -- Terms are not stored normalised.
    -- Terms of different types must not be equal, because that results in
    -- ill-typed equations and bad things happening in the pruner.
    tm_tree   :: Map Type (DecisionTree testcase result term) }

makeLensAs ''Terms [("tm_tree", "tree")]

treeForType :: Type -> Lens (Terms testcase result term) (DecisionTree testcase result term)
treeForType ty = reading (\Terms{..} -> keyDefault ty tm_empty # tree)

initialState ::
  (term -> testcase -> result) ->
  Terms testcase result term
initialState eval =
  Terms {
    tm_empty = empty eval,
    tm_terms = Map.empty,
    tm_tree = Map.empty }

data Result term =
    -- Discovered a new law.
    Discovered (Prop term)
    -- Term is equal to an existing term so redundant.
  | Knew (Prop term)
  | Singleton

-- The Prop returned is always t :=: u, where t is the term passed to explore
-- and u is the representative of t's equivalence class, not normalised.
-- The representatives of the equivalence classes are guaranteed not to change.
--
-- Discovered properties are not added to the pruner.
explore :: (Typed term, Ord term, Ord result, MonadTester testcase term m, MonadPruner term m) =>
  term -> StateT (Terms testcase result term) m (Result term)
explore t = do
  norm <- normaliser
  exp norm $ \prop -> do
    res <- test prop
    case res of
      Nothing -> do
        return (Discovered prop)
      Just tc -> do
        treeForType ty %= addTestCase tc
        exp norm $
          error "returned counterexample failed to falsify property"

  where
    ty = typ t
    exp norm found = do
      tm@Terms{..} <- get
      case Map.lookup t' tm_terms of
        Just u -> return (Knew (t === u))
        Nothing ->
          case insert t (tm ^. treeForType ty) of
            Distinct tree -> do
              put (setL (treeForType ty) tree tm { tm_terms = Map.insert t' t tm_terms })
              return Singleton
            EqualTo u
              -- tm_terms is not kept normalised wrt the discovered laws;
              -- instead, we normalise it lazily like so.
              | t' == u' -> do
                put tm { tm_terms = Map.insert u' u tm_terms }
                return (Knew prop)
              -- Ask QuickCheck for a counterexample to the property.
              | otherwise -> found prop
              where
                u' = norm u
                prop = t === u
      where
        t' = norm t
