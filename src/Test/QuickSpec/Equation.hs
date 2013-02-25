-- | Equations.

module Test.QuickSpec.Equation where

import Test.QuickSpec.Term
import Test.QuickSpec.Signature hiding (vars)
import Test.QuickSpec.Utils.Typed
import Data.Monoid
import Data.List

data Equation = Term :=: Term deriving (Eq, Ord)

showEquation :: Sig -> Equation -> String
showEquation sig (t :=: u) =
  show (f t) ++ " == " ++ show (f u)
  where f = disambiguate sig (vars t ++ vars u)

instance Show Equation where
  show = showEquation mempty

equations :: [[Tagged Term]] -> [Equation]
equations = sort . concatMap (toEquations . map erase)
  where toEquations (x:xs) = [y :=: x | y <- xs]
