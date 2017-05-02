-- Theory exploration which accepts one term at a time.
{-# LANGUAGE RecordWildCards, CPP, FlexibleContexts #-}
module QuickSpec.Explore.Terms where

#include "errors.h"
import qualified Data.Set as Set
import Data.Set(Set)
import QuickSpec.Prop
import QuickSpec.Pruner
import QuickSpec.Tester

data State term =
  State {
    st_terms  :: Set term,
    st_pruner :: Pruner term,
    st_tester :: Tester term }

explore :: Ord term =>
  term -> State term -> (State term, Maybe (Prop term))
explore t s@State{..}
  | t' `Set.member` st_terms = (s, Nothing)
  | otherwise =
    case test st_tester t of
      Distinct tester ->
        (s { st_tester = tester, st_terms = Set.insert t' st_terms }, Nothing)
      EqualTo u ->
        (s { st_pruner = add st_pruner ([] :=>: t :=: u) }, Just ([] :=>: t :=: u))
  where
    t' = normalise st_pruner t
