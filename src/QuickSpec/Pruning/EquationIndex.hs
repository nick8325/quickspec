module QuickSpec.Pruning.EquationIndex where

import QuickSpec.Base
import qualified QuickSpec.Pruning.RuleIndex as RuleIndex
import QuickSpec.Pruning.RuleIndex(RuleIndex)
import QuickSpec.Pruning.Equation
import QuickSpec.Pruning.Queue
import Data.Rewriting.Rule

newtype EquationIndex f v = EquationIndex (RuleIndex f v) deriving Show

empty :: EquationIndex f v
empty = EquationIndex RuleIndex.empty

insert ::
  (Ord f, Ord v, Numbered v) => Label -> Equation f v -> EquationIndex f v -> EquationIndex f v
insert label (l :==: r) (EquationIndex idx) =
  EquationIndex (RuleIndex.insert label (Rule l r) idx)

delete ::
  (Ord f, Ord v, Numbered v) => Label -> Equation f v -> EquationIndex f v -> EquationIndex f v
delete label (l :==: r) (EquationIndex idx) =
  EquationIndex (RuleIndex.delete label (Rule l r) idx)

lookup ::
  (Ord f, Ord v, Numbered v) => Tm f v -> EquationIndex f v -> [Labelled (Equation f v)]
lookup t (EquationIndex idx) =
  map (fmap unorient) (RuleIndex.lookup t idx ++ RuleIndex.lookup t (RuleIndex.invert idx))

elems :: EquationIndex f v -> [Labelled (Equation f v)]
elems (EquationIndex idx) = map (fmap unorient) (RuleIndex.elems idx)
