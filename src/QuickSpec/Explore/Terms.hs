-- Theory exploration which accepts one term at a time.
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards #-}
module QuickSpec.Explore.Terms where

import qualified Data.Set as Set
import Data.Set(Set)
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Testing
import QuickSpec.Testing.DecisionTree hiding (Result)

data State testcase result term =
  State {
    st_terms  :: Set term,
    st_tree   :: DecisionTree testcase result term }

initialState ::
  (term -> testcase -> result) ->
  State testcase result term
initialState eval =
  State {
    st_terms = Set.empty,
    st_tree = empty eval }

explore :: (Ord term, Ord result, Tester testcase term m, Pruner term m) =>
  term -> State testcase result term ->
  m (State testcase result term, [term], [Prop term])
explore t s = do
  norm <- normaliser
  exp norm True s
  where
    exp norm testMore s@State{..}
      | t' `Set.member` st_terms = return (s, [], [])
      | otherwise =
        case insert t st_tree of
          Distinct tree ->
            return (s { st_tree = tree, st_terms = Set.insert t' st_terms }, [t], [])
          EqualTo u
            -- st_terms is not kept normalised wrt the discovered laws;
            -- instead, we normalise it lazily like so.
            | t' == u' ->
              return (s { st_terms = Set.insert u' (Set.delete u st_terms) }, [], [])
            -- Ask QuickCheck for a counterexample to the property.
            | otherwise -> do
                res <- test prop
                case res of
                  Nothing -> do
                    add prop
                    return (s, [], [prop])
                  Just tc -> do
                    -- Here we make testMore = False: if for some reason
                    -- the discovered counterexample fails to falsify the
                    -- equation, we don't want to run QuickCheck again!
                    exp norm False s { st_tree = addTestCase tc st_tree }
            where
              u' = norm u
              prop = t === u
      where
        t' = norm t
