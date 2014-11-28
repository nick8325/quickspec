{-# LANGUAGE TypeFamilies #-}
module QuickSpec.Pruning.Equation where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Utils
import Data.Ord
import Control.Monad
import Data.Rewriting.Rule hiding (isVariantOf)
import QuickSpec.Pruning.Constraints
import Data.Maybe
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set

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
  | Measure l >= Measure r = l :==: r
  | otherwise = r :==: l

unorient :: Rule f v -> Equation f v
unorient (Rule l r) = l :==: r

orient :: (Sized f, Ord f, Ord v, Numbered v) => Equation f v -> [Constrained (Rule f v)]
orient (l :==: r) = rule l r ++ concat [rule r l | not (l `isVariantOf` r)]
  where
    rule l r = add (Constraint Less r l) (unconstrained (Rule l r))

bothSides :: (Tm f v -> Tm f v) -> Equation f v -> Equation f v
bothSides f (t :==: u) = f t :==: f u

trivial :: (Ord f, Ord v) => Equation f v -> Bool
trivial (t :==: u) = t == u

equationSize :: Sized f => Equation f v -> Int
equationSize (t :==: u) = size t `max` size u
