module QuickSpec.Pruning.Rewrite where

import QuickSpec.Base
import QuickSpec.Term
import Data.Rewriting.Rule
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import qualified QuickSpec.Pruning.Equations as Equations
import QuickSpec.Pruning.Equations(Equations)
import QuickSpec.Pruning.Equation
import Data.Maybe

type Strategy f v = Tm f v -> [Tm f v]

normaliseWith :: Strategy f v -> Tm f v -> Tm f v
normaliseWith strat t =
  case strat t of
    [] -> t
    (r:_) -> normaliseWith strat r

anywhere :: Strategy f v -> Strategy f v
anywhere strat t = strat t ++ nested (anywhere strat) t

nested :: Strategy f v -> Strategy f v
nested strat Var{} = []
nested strat (Fun f xs) = map (Fun f) (combine xs (map strat xs))
  where
    combine [] [] = []
    combine (x:xs) (ys:yss) =
      [ y:xs | y <- ys ] ++ [ x:zs | zs <- combine xs yss ]

ordered :: (Sized f, Ord f, Ord v) => Strategy f v -> Strategy f v
ordered strat t = [u | u <- strat t, u `simplerThan` t]

tryRule :: (Ord f, Ord v) => Rule f v -> Strategy f v
tryRule rule t = do
  sub <- maybeToList (match (lhs rule) t)
  return (subst sub (rhs rule))

tryRules :: (Ord f, Ord v) => Index (Rule f v) -> Strategy f v
tryRules rules t = map rhs (Index.lookup t rules)

tryEquation :: (Ord f, Ord v) => Equation f v -> Strategy f v
tryEquation (t :==: u) v =
  tryRule (Rule t u) v ++ tryRule (Rule u t) v

tryEquations :: (Ord f, Ord v) => Equations f v -> Strategy f v
tryEquations eqns t = Equations.lookup t eqns
