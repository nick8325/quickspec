module QuickSpec.Pruning.Rewrite where

import QuickSpec.Base
import QuickSpec.Term
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import QuickSpec.Pruning.Equation
import QuickSpec.Pruning.Constraints
import Data.Maybe
import Data.Set(Set)
import QuickSpec.Pruning.Queue
import Control.Monad
import Data.Rewriting.Rule
import Debug.Trace

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

tryRule :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Context f v -> Constrained (Rule f v) -> Strategy f v
tryRule ctx rule t = do
  sub <- maybeToList (match (lhs (constrained rule)) t)
  rule' <- split (substf (evalSubst sub) rule)
  guard (implies ctx (context rule'))
  return (rhs (constrained rule'))

tryRules :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Context f v -> Index (Labelled (Constrained (Rule f v))) -> Strategy f v
tryRules ctx rules t = do
  rule <- map peel (Index.lookup t rules) >>= split
  guard (implies ctx (context rule))
  traceM (prettyShow rule ++ " in context " ++ prettyShow ctx)
  return (rhs (constrained rule))
