-- Theory exploration which accepts one term at a time.
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards #-}
module QuickSpec.Explore.Terms where

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Testing
import QuickSpec.Testing.DecisionTree hiding (Result, Singleton)

data State testcase result term =
  State {
    -- Terms already explored. These are stored in the *values* of the map.
    -- The keys are those terms but normalised.
    -- We do it like this so that explore can guarantee to always return
    -- the same representative for each equivalence class (see below).
    st_terms  :: Map term term,
    -- Decision tree mapping test case results to terms.
    -- Terms are not stored normalised.
    st_tree   :: DecisionTree testcase result term }

initialState ::
  (term -> testcase -> result) ->
  State testcase result term
initialState eval =
  State {
    st_terms = Map.empty,
    st_tree = empty eval }

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
explore :: (Ord term, Ord result, MonadTester testcase term m, MonadPruner term m) =>
  term -> State testcase result term ->
  m (State testcase result term, Result term)
explore t s = do
  norm <- normaliser
  exp norm s $ \prop -> do
    res <- test prop
    case res of
      Nothing -> do
        return (s, Discovered prop)
      Just tc -> do
        exp norm s { st_tree = addTestCase tc (st_tree s) } $
          error "returned counterexample failed to falsify property"
          
  where
    exp norm s@State{..} found =
      case Map.lookup t' st_terms of
        Just u -> return (s, Knew (t === u))
        Nothing ->
          case insert t st_tree of
            Distinct tree ->
              return (s { st_tree = tree, st_terms = Map.insert t' t st_terms }, Singleton)
            EqualTo u
              -- st_terms is not kept normalised wrt the discovered laws;
              -- instead, we normalise it lazily like so.
              | t' == u' ->
                return (s { st_terms = Map.insert u' u st_terms }, Knew prop)
              -- Ask QuickCheck for a counterexample to the property.
              | otherwise -> found prop
              where
                u' = norm u
                prop = t === u
      where
        t' = norm t
