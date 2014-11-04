{-# LANGUAGE TypeFamilies #-}
module QuickSpec.Pruning.Equations where

import QuickSpec.Base
import QuickSpec.Term
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Equation
import Control.Monad
import qualified Data.Rewriting.Rule as Rule

data Equations f v =
  Equations {
    left  :: Index.Index (Rule.Rule f v),
    right :: Index.Index (Rule.Rule f v) }

empty :: Equations f v
empty = Equations Index.empty Index.empty

insert :: (Ord f, Ord v, Numbered v) => Equation f v -> Equations f v -> Equations f v
insert (t :==: u) (Equations left right) =
  Equations {
    left  = Index.insert (Rule.Rule t u) left,
    right = Index.insert (Rule.Rule u t) right }

delete :: (Ord f, Ord v, Numbered v) => Equation f v -> Equations f v -> Equations f v
delete (t :==: u) (Equations left right) =
  Equations {
    left  = Index.delete (Rule.Rule t u) left,
    right = Index.delete (Rule.Rule t u) right }

match :: (Sized f, Ord f, Ord v) => Tm f v -> Equations f v -> [Rule.Rule f v]
match t (Equations left right) = do
  rule <- Index.lookup t left ++ Index.lookup t right
  guard (Rule.rhs rule `simplerThan` t)
  return rule

elems :: Equations f v -> [Equation f v]
elems set =
  [ t :==: u | Rule.Rule t u <- Index.elems (left set) ]
