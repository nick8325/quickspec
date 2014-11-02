module QuickSpec.Pruning.RuleSet where

import QuickSpec.Base
import qualified QuickSpec.Pruning.Indexing as Indexing
import qualified Data.Rewriting.Rule as Rule

type RuleSet f v = Indexing.Index f v (Tm f v)

empty :: RuleSet f v
empty = Indexing.empty

insert :: (Ord f, Ord v) => Rule.Rule f v -> RuleSet f v -> RuleSet f v
insert r s = Indexing.insert (Rule.lhs r) (Rule.rhs r) s

delete :: (Ord f, Ord v) => Rule.Rule f v -> RuleSet f v -> RuleSet f v
delete r s = Indexing.delete (Rule.lhs r) (Rule.rhs r) s

lookup :: (Ord f, Ord v) => Tm f v -> RuleSet f v -> [Rule.Rule f v]
lookup t s = do
  res <- Indexing.lookup t s
  return (Rule.Rule t (subst (Indexing.subst res) (Indexing.result res)))
