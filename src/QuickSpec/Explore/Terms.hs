-- Theory exploration which accepts one term at a time.
{-# LANGUAGE RecordWildCards, CPP, FlexibleContexts #-}
module QuickSpec.Explore.Terms where

#include "errors.h"
import qualified Data.Set as Set
import Data.Set(Set)
import QuickSpec.Prop
import QuickSpec.Pruner
import QuickSpec.Testing.DecisionTree

data State testcase result term =
  State {
    st_terms  :: Set term,
    st_pruner :: Pruner term,
    st_tree   :: DecisionTree testcase result term,
    st_tester :: Prop term -> Maybe testcase }

explore :: (Ord term, Ord result) =>
  term -> State testcase result term ->
  (State testcase result term, Maybe (Prop term))
explore t s = exp True s
  where
    exp testMore s@State{..}
      | t' `Set.member` st_terms = (s, Nothing)
      | otherwise =
        case insert t st_tree of
          Distinct tree ->
            (s { st_tree = tree, st_terms = Set.insert t' st_terms }, Nothing)
          EqualTo u
            -- st_terms is not kept normalised wrt the discovered laws;
            -- instead, we normalise it lazily like so.
            | t' == u' ->
              exp testMore s { st_terms = Set.insert u' (Set.delete u st_terms) }
            -- Ask QuickCheck for a counterexample to the property.
            | testMore,
              Just tc <- st_tester prop ->
                -- Here we make testMore = False: if for some reason
                -- the discovered counterexample fails to falsify the
                -- equation, we don't want to run QuickCheck again!
                exp False s { st_tree = addTestCase tc st_tree }
            | otherwise ->
                (s { st_pruner = add st_pruner prop }, Just prop)
            where
              u' = normalise st_pruner u
              prop = [] :=>: t' :=: u'
      where
        t' = normalise st_pruner t
