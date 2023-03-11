-- Theory exploration which accepts one term at a time.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards #-}
module QuickSpec.Internal.Explore.Terms where

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import QuickSpec.Internal.Term
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Type
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Testing.DecisionTree hiding (Result, Singleton)
import Control.Monad.Trans.State.Strict hiding (State)
import Data.Lens.Light
import QuickSpec.Internal.Utils
import QuickSpec.Internal.Terminal

data Terms testcase result term norm =
  Terms {
    -- Empty decision tree.
    tm_empty :: DecisionTree testcase result term,
    -- Terms already explored. These are stored in the *values* of the map.
    -- The keys are those terms but normalised.
    -- We do it like this so that explore can guarantee to always return
    -- the same representative for each equivalence class (see below).
    tm_terms  :: Map norm term,
    -- Decision tree mapping test case results to terms.
    -- Terms are not stored normalised.
    -- Terms of different types must not be equal, because that results in
    -- ill-typed equations and bad things happening in the pruner.
    tm_tree   :: Map Type (DecisionTree testcase result term) }

tree = lens tm_tree (\x y -> y { tm_tree = x })

treeForType :: Type -> Lens (Terms testcase result term norm) (DecisionTree testcase result term)
treeForType ty = reading (\Terms{..} -> keyDefault ty tm_empty # tree)

initialState ::
  (term -> testcase -> Maybe result) ->
  Terms testcase result term norm
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
explore :: (Pretty term, Typed term, Ord norm, Ord result, MonadTester testcase term m, MonadPruner term norm m, MonadTerminal m) =>
  term -> StateT (Terms testcase result term norm) m (Result term)
explore t = do
  res <- explore' t
  --case res of
  --  Discovered prop -> putLine ("discovered " ++ prettyShow prop)
  --  Knew prop -> putLine ("knew " ++ prettyShow prop)
  --  Singleton -> putLine ("singleton " ++ prettyShow t)
  return res
explore' :: (Pretty term, Typed term, Ord norm, Ord result, MonadTester testcase term m, MonadPruner term norm m) =>
  term -> StateT (Terms testcase result term norm) m (Result term)
explore' t = do
  norm <- normaliser
  exp norm $ \prop -> do
    res <- test prop
    case res of
      Nothing ->
        return Singleton
      Just TestPassed -> do
        return (Discovered prop)
      Just (TestFailed tc) -> do
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
