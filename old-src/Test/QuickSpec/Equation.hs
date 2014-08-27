-- | Equations.

module Test.QuickSpec.Equation where

import Test.QuickSpec.Term
import Test.QuickSpec.Signature hiding (vars)
import Test.QuickSpec.Utils.Typed
import Data.Monoid
import Data.List
import Data.Ord

data Equation = Term :=: Term deriving (Eq, Ord)

showEquation :: Sig -> Equation -> String
showEquation sig (t :=: u) =
  show (mapVars f t) ++ " == " ++ show (mapVars f u)
  where f = disambiguate sig (vars t ++ vars u)

instance Show Equation where
  show = showEquation mempty

data TypedEquation a = Expr a :==: Expr a

eraseEquation :: TypedEquation a -> Equation
eraseEquation (e1 :==: e2) = term e1 :=: term e2

instance Eq (TypedEquation a) where
  e1 == e2 = e1 `compare` e2 == EQ

instance Ord (TypedEquation a) where
  compare = comparing eraseEquation

instance Show (TypedEquation a) where
  show = show . eraseEquation

showTypedEquation :: Sig -> TypedEquation a -> String
showTypedEquation sig e = showEquation sig (eraseEquation e)

equations :: [Several Expr] -> [Some TypedEquation]
equations = sortBy (comparing (some eraseEquation)) .
            concatMap (several toEquations)
  where toEquations (x:xs) = [Some (y :==: x) | y <- xs]
