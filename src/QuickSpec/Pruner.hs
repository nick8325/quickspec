-- A type of pruners.
module QuickSpec.Pruner where

import QuickSpec.Prop

data Pruner term =
  Pruner {
    normalise :: term -> term,
    add :: Prop term -> Pruner term }

makePruner ::
  (pruner -> term -> term) ->
  (Prop term -> pruner -> pruner) ->
  pruner -> Pruner term
makePruner norm add state =
  Pruner {
    normalise = \t -> norm state t,
    add = \p -> makePruner norm add (add p state) }
