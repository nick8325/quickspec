{-# LANGUAGE TypeFamilies #-}
module QuickSpec.Pruning.Equation where

import QuickSpec.Base
import QuickSpec.Pruning.Constraints
import QuickSpec.Term
import Control.Monad
import Data.Rewriting.Rule hiding (isVariantOf)

data Equation f v = Tm f v :==: Tm f v deriving (Eq, Ord, Show)
type EquationOf a = Equation (ConstantOf a) (VariableOf a)

instance Symbolic (Equation f v) where
  type ConstantOf (Equation f v) = f
  type VariableOf (Equation f v) = v
  termsDL (t :==: u) = termsDL t `mplus` termsDL u
  substf sub (t :==: u) = substf sub t :==: substf sub u

instance (PrettyTerm f, Pretty v) => Pretty (Equation f v) where
  pretty (x :==: y) = hang (pretty x <+> text "=") 2 (pretty y)

order :: (Sized f, Ord f, Ord v) => Equation f v -> Equation f v
order (l :==: r)
  | measure l >= measure r = l :==: r
  | otherwise = r :==: l

unorient :: Rule f v -> Equation f v
unorient (Rule l r) = l :==: r

orient :: (Sized f, Ord f, Ord v, Numbered v) => Equation f v -> [Constrained (Rule f v)]
orient (l :==: r) =
  case orientTerms l r of
    Just GT -> [unconstrained (Rule l r)]
    Just LT -> [unconstrained (Rule r l)]
    Just EQ -> []
    Nothing -> rule l r ++ concat [rule r l | not (l `isVariantOf` r)]
  where
    rule l r = add (Less r l) (unconstrained (Rule l r))

bothSides :: (Tm f v -> Tm f v) -> Equation f v -> Equation f v
bothSides f (t :==: u) = f t :==: f u

trivial :: (Ord f, Ord v) => Equation f v -> Bool
trivial (t :==: u) = t == u

equationSize :: Sized f => Equation f v -> Int
equationSize (t :==: u) = size t `max` size u
