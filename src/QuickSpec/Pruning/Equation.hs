{-# LANGUAGE TypeFamilies #-}
module QuickSpec.Pruning.Equation where

import QuickSpec.Base
import QuickSpec.Term
import Data.Ord
import Control.Monad
import qualified Data.Rewriting.Rule as Rule

data Equation f v = Tm f v :==: Tm f v deriving (Eq, Show)
type EquationOf a = Equation (ConstantOf a) (VariableOf a)

instance (Sized f, Ord f, Ord v) => Ord (Equation f v) where
  compare = comparing (\(l :==: r) -> (Measure l, Measure r))

instance Symbolic (Equation f v) where
  type ConstantOf (Equation f v) = f
  type VariableOf (Equation f v) = v
  termsDL (t :==: u) = termsDL t `mplus` termsDL u
  substf sub (t :==: u) = substf sub t :==: substf sub u

(===) :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Equation f v
x === y
  | Measure x < Measure y = y :==: x
  | otherwise = x :==: y

orient :: (Sized f, Ord f, Ord v) => Equation f v -> Maybe (Rule.Rule f v)
orient eq@(l :==: r) =
  case orientTerms l r of
    Just LT -> Just (Rule.Rule r l)
    Just GT -> Just (Rule.Rule l r)
    _       -> Nothing

instance (PrettyTerm f, Pretty v) => Pretty (Equation f v) where
  pretty (x :==: y) = hang (pretty x <+> text "=") 2 (pretty y)
