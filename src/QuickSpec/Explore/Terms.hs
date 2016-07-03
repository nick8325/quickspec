-- Theory exploration which accepts one term at a time.
{-# LANGUAGE RecordWildCards, CPP #-}
module QuickSpec.Explore.Terms where

#include "errors.h"
import qualified Data.Set as Set
import Data.Set(Set)
import QuickSpec.Term
import QuickSpec.Prop
import QuickSpec.Pruner
import QuickSpec.Tester

data State f pruner tester =
  State {
    st_terms  :: Set (Term f),
    st_pruner :: pruner,
    st_tester :: tester }

explore :: (Ord f, Pruner f pruner, Tester f tester) =>
  Term f -> State f pruner tester -> (State f pruner tester, Maybe (Prop (Term f)))
explore t s@State{..}
  | t' `Set.member` st_terms = (s, Nothing)
  | otherwise =
    case testTerm t st_tester of
      Distinct tester ->
        (s { st_tester = tester, st_terms = Set.insert t' st_terms }, Nothing)
      EqualTo u
        | t' == normalise st_pruner u ->
          (s { st_terms = Set.insert t' st_terms }, Nothing)
        | otherwise ->
          (s { st_pruner = add ([] :=>: t :=: u) st_pruner }, Just ([] :=>: t :=: u))
  where
    t' = normalise st_pruner t
