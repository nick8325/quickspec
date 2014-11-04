module QuickSpec.Pruning.RuleSet where

import QuickSpec.Base
import qualified QuickSpec.Pruning.Indexing as Indexing
import qualified Data.Rewriting.Rule as Rule

type RuleSet f v = Indexing.Index f v (Rule.Rule f v)

empty :: RuleSet f v
empty = Indexing.empty

insert :: (Ord f, Ord v) => Rule.Rule f v -> RuleSet f v -> RuleSet f v
insert r s = Indexing.insert (Rule.lhs r) r s

delete :: (Ord f, Ord v) => Rule.Rule f v -> RuleSet f v -> RuleSet f v
delete r s = Indexing.delete (Rule.lhs r) r s

match :: (Ord f, Ord v) => Tm f v -> RuleSet f v -> [Rule.Rule f v]
match t s = do
  res <- Indexing.lookup t s
  return (Rule.Rule t (subst (Indexing.subst res) (Rule.rhs (Indexing.result res))))

elems :: RuleSet f v -> [Rule.Rule f v]
elems = Indexing.elems
