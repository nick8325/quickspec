{-# LANGUAGE TypeFamilies #-}
module QuickSpec.Pruning.Rule where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Pruning
import QuickSpec.Pruning.Constraints
import Control.Monad
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as Set
import qualified Data.Rewriting.Rule as Rule

-- A rule only ever has one constraint,
-- in the worst case: rhs rule > lhs rule.
data Rule f v =
  Rule {
    constraint :: Maybe (Constraint f v),
    lhs :: Tm f v,
    rhs :: Tm f v }
  deriving (Eq, Ord, Show)

ruleConstraints :: (Ord f, Ord v) => Rule f v -> Set (Constraint f v)
ruleConstraints (Rule Nothing _ _) = Set.empty
ruleConstraints (Rule (Just rule) _ _) = Set.singleton rule

toRewritingRule :: Rule f v -> Rule.Rule f v
toRewritingRule rule = Rule.Rule (lhs rule) (rhs rule)

instance Symbolic (Rule f v) where
  type ConstantOf (Rule f v) = f
  type VariableOf (Rule f v) = v
  termsDL (Rule cond lhs rhs) =
    termsDL lhs `mplus` termsDL rhs `mplus`
    fromMaybe mzero (fmap termsDL cond)
  substf sub (Rule cond lhs rhs) =
    Rule (fmap (substf sub) cond) (substf sub lhs) (substf sub rhs)

instance (PrettyTerm f, Pretty v) => Pretty (Rule f v) where
  pretty (Rule cond lhs rhs) =
    sep $
      [pretty lhs <+> text "->", nest 2 (pretty rhs)] ++
      case cond of
        Nothing -> []
        Just cond -> [nest 2 (text "when" <+> pretty cond)]

rule :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> Maybe (Rule f v)
rule lhs rhs =
  case orientTerms lhs rhs of
    Just GT -> Just (Rule Nothing lhs rhs)
    Just EQ | lhs > rhs -> Just (Rule Nothing lhs rhs) -- typing rule
    Just _  -> Nothing
    Nothing -> Just (Rule (Just (less rhs lhs)) lhs rhs)

ruleAllowed :: (Sized f, Ord f, Ord v, Numbered v) => Set (Constraint f v) -> Rule f v -> Bool
ruleAllowed conds (Rule Nothing _ _) = True
ruleAllowed conds (Rule (Just cond) _ _) = subsumes conds cond
