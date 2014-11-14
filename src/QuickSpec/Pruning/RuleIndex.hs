module QuickSpec.Pruning.RuleIndex where

import QuickSpec.Base
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import QuickSpec.Pruning.Queue
import QuickSpec.Pruning.Equation
import Data.Rewriting.Rule

data RuleIndex f v =
  RuleIndex {
    forward  :: Index (Labelled (Rule f v)),
    back     :: Index (Labelled (Rule f v)) }
  deriving Show

empty :: RuleIndex f v
empty = RuleIndex Index.empty Index.empty

insert ::
  (Ord f, Ord v, Numbered v) => Label -> Rule f v -> RuleIndex f v -> RuleIndex f v
insert label (Rule l r) (RuleIndex forward back) =
  RuleIndex
    (Index.insert (Labelled label (Rule l r)) forward)
    (Index.insert (Labelled label (Rule r l)) back)

delete ::
  (Ord f, Ord v, Numbered v) => Label -> Rule f v -> RuleIndex f v -> RuleIndex f v
delete label (Rule l r) (RuleIndex forward back) =
  RuleIndex
    (Index.delete (Labelled label (Rule l r)) forward)
    (Index.delete (Labelled label (Rule r l)) back)

lookup ::
  (Ord f, Ord v, Numbered v) => Tm f v -> RuleIndex f v -> [Labelled (Rule f v)]
lookup t (RuleIndex forward _) =
  Index.lookup t forward

elems :: RuleIndex f v -> [Labelled (Rule f v)]
elems (RuleIndex forward _) = Index.elems forward

invert :: RuleIndex f v -> RuleIndex f v
invert (RuleIndex forward back) = RuleIndex back forward
