{-# LANGUAGE TypeFamilies #-}
module QuickSpec.Pruning.Equation where

import QuickSpec.Base
import QuickSpec.Term
import Data.Ord
import Control.Monad
import qualified Data.Rewriting.Rule as Rule

data Equation f v = Tm f v :==: Tm f v deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a) (VariableOf a)

instance Symbolic (Equation f v) where
  type ConstantOf (Equation f v) = f
  type VariableOf (Equation f v) = v
  termsDL (t :==: u) = termsDL t `mplus` termsDL u
  substf sub (t :==: u) = substf sub t :==: substf sub u

instance (PrettyTerm f, Pretty v) => Pretty (Equation f v) where
  pretty (x :==: y) = hang (pretty x <+> text "=") 2 (pretty y)

order :: (Sized f, Ord f, Ord v) => Equation f v -> Rule.Rule f v
order (l :==: r)
  | Measure l >= Measure r =
    Rule.Rule l r
  | otherwise =
    Rule.Rule r l

unorient :: Rule.Rule f v -> Equation f v
unorient (Rule.Rule l r) = l :==: r

orient :: (Sized f, Ord f, Ord v) => Equation f v -> Maybe (Rule.Rule f v)
orient (l :==: r) =
  case orientTerms l r of
    Just LT -> Just (Rule.Rule r l)
    Just GT -> Just (Rule.Rule l r)
    _       -> Nothing

bothSides :: (Tm f v -> Tm f v) -> Equation f v -> Equation f v
bothSides f (t :==: u) = f t :==: f u

trivial :: (Ord f, Ord v) => Equation f v -> Bool
trivial (t :==: u) = t == u

equationSize :: Sized f => Equation f v -> Int
equationSize (t :==: u) = size t `max` size u
