module QuickSpec.Pruning.Equations where

import QuickSpec.Base
import QuickSpec.Pruning.Equation
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import Data.Rewriting.Rule hiding (left, right)

data Equations f v =
  Equations {
    left  :: Index (Rule f v),
    right :: Index (Rule f v) }

empty :: Equations f v
empty = Equations Index.empty Index.empty

insert :: (Ord f, Ord v, Numbered v) => Equation f v -> Equations f v -> Equations f v
insert (t :==: u) (Equations left right) =
  Equations {
    left  = Index.insert (Rule t u) left,
    right = Index.insert (Rule u t) right }

delete :: (Ord f, Ord v, Numbered v) => Equation f v -> Equations f v -> Equations f v
delete (t :==: u) (Equations left right) =
  Equations {
    left  = Index.delete (Rule t u) left,
    right = Index.delete (Rule u t) right }

lookup :: (Ord f, Ord v) => Tm f v -> Equations f v -> [Tm f v]
lookup t (Equations left right) =
  map rhs (Index.lookup t left ++ Index.lookup t right)

elems :: (Ord f, Ord v) => Equations f v -> [Equation f v]
elems idx = map unorient (Index.elems (left idx))
