{-# LANGUAGE TypeOperators, TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, ConstraintKinds #-}
module QuickSpec.Pruning.Constraints where

#include "errors.h"
import QuickSpec.Base
import qualified QuickSpec.Pruning.FourierMotzkin as FM
import QuickSpec.Pruning.FourierMotzkin hiding (Term(..), trace, Stop, solve, implies, Unsolvable)
import QuickSpec.Term
import QuickSpec.Utils
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.Maybe
import Data.Ord
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Rewriting.Substitution.Type as Subst
import Data.List

import QuickSpec.Pruning
import Data.Rewriting.Rule(Rule(Rule))
data F = F String | Ty deriving (Eq, Ord, Show)
instance Pretty F where
  pretty (F x) = text x
  pretty Ty    = text "@"
instance PrettyTerm F where termStyle _ = Infix 5
instance Sized F where
  funSize (F _) = 1
  funSize Ty    = 0
  funArity Ty = 1
  funArity _ = 2
t, u :: Tm F PruningVariable
--t = Fun (F "sx") []
--u = Fun Ty [t]
--t = Fun (F "+") [Var 0, Var 1]
--u = Fun (F "+") [Var 1, Var 0]
(t, u) = (f (Var 0) (Var 1), f (Var 1) (Var 0))
  where
    f x y = Fun (F "*") [x, Fun (F "+") [y, Fun (F "+") [y, y]]]
r1 = Constrained (toContext (Less u t)) (Rule t u)
r2 = Constrained (toContext (Less t u)) (Rule u t)
form :: Formula F PruningVariable
form = Less (Var 0) (Fun (F "*") [Var 1, Var 2]) &&& Less (Var 0) (Var 1)
r = Constrained (toContext form) (Fun Ty [Var 0, Var 1, Var 2])

-- Constrained things.
data Constrained a =
  Constrained {
    context     :: ContextOf a,
    constrained :: a }

instance (PrettyTerm (ConstantOf a), Pretty (VariableOf a), Pretty a) => Pretty (Constrained a) where
  pretty (Constrained (Context { formula = FTrue }) x) = pretty x
  pretty (Constrained ctx x) =
    hang (pretty x) 2 (text "when" <+> pretty ctx)

deriving instance (Eq a, Eq (ConstantOf a), Eq (VariableOf a)) => Eq (Constrained a)
deriving instance (Ord a, Ord (ConstantOf a), Ord (VariableOf a)) => Ord (Constrained a)
deriving instance (Show a, Show (VariableOf a), Show (ConstantOf a)) => Show (Constrained a)

instance (Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Symbolic a) => Symbolic (Constrained a) where
  type ConstantOf (Constrained a) = ConstantOf a
  type VariableOf (Constrained a) = VariableOf a

  termsDL x =
    termsDL (constrained x) `mplus`
    termsDL (context x)

  substf sub (Constrained ctx x) =
    Constrained (substf sub ctx) (substf sub x)

reduce :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> Constrained a
reduce x =
  case split x of
    [y] | simple (formula (context y)) -> y
    _ -> x
  where
    simple (p :&: q) = simple p && simple q
    simple (p :|: q) = simple p || simple q
    simple FTrue = True
    simple FFalse = True
    simple Less{} = True
    simple _ = False

split :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> [Constrained a]
split (Constrained ctx x) =
  case runM simplify (formula ctx) of
    Equal t u p q ->
      let Just sub = unify t u in
      split (make q) ++ split (substf (evalSubst sub) (make (prune p)))
    p :|: q ->
      split (make p) ++ split (make q)
    p -> [make p | satisfiable (solved (toContext p))]
  where
    make ctx = Constrained (toContext ctx) x
    prune (Equal t u p q) = Equal t u (prune p) (prune q)
    prune (p :|: q) = prune p ||| prune q
    prune p
      | satisfiable (solved (toContext p)) = p
      | otherwise = FFalse

mainSplit :: (Sized f, Numbered v, Ord f, Ord v) => Formula f v -> Formula f v
mainSplit p =
  case mainSplits p of
    [] -> FFalse
    (q:_) -> q

mainSplits :: (Sized f, Numbered v, Ord f, Ord v) => Formula f v -> [Formula f v]
mainSplits p =
  case runM simplify p of
    Equal t u p q -> mainSplits q
    p :|: q -> mainSplits p ++ mainSplits q
    p | satisfiable (solve p) -> [p]
      | otherwise -> []

neg :: (Symbolic a, Sized (ConstantOf a), Numbered (VariableOf a), Ord (ConstantOf a), Ord (VariableOf a)) => Constrained a -> Constrained a
neg = runM $ \x -> do
  f <- negFormula (formula (context x))
  return x { context = toContext f }

-- Contexts (sets of constraints).
type ContextOf a = Context (ConstantOf a) (VariableOf a)
data Context f v =
  Context {
    formula :: Formula f v,
    solved  :: Solved f v,
    model   :: Map v (Extended f v) }
  deriving Show

toContext :: (Sized f, Ord f, Ord v) => Formula f v -> Context f v
toContext x = Context x s (toModel s)
  where
    s = solve x

instance (Eq f, Eq v) => Eq (Context f v) where
  x == y = formula x == formula y
instance (Ord f, Ord v) => Ord (Context f v) where
  compare = comparing formula
instance (PrettyTerm f, Pretty v) => Pretty (Context f v) where
  pretty = pretty . formula
instance (Sized f, Ord f, Ord v) => Symbolic (Context f v) where
  type ConstantOf (Context f v) = f
  type VariableOf (Context f v) = v
  termsDL ctx = termsDL (formula ctx)
  substf sub ctx = toContext (substf sub (formula ctx))

-- Formulas.
type FormulaOf a = Formula (ConstantOf a) (VariableOf a)
data Formula f v =
  -- After calling split, formulas are in the following form:
  -- * No occurrences of Equal.
  -- * HeadIs and Less can only be applied to variables.
  -- * No tautological or impossible literals.
    FTrue
  | FFalse
  | Formula f v :&: Formula f v
  | Formula f v :|: Formula f v
  | Size (Bound (FM.Term v))
  | HeadIs Sense (Tm f v) f
  | Less (Tm f v) (Tm f v)
    -- Equal t u p q represents (t = u & p) | q.
    -- The smart constructors (|||) and (&&&) lift
    -- Equal to the top level.
  | Equal (Tm f v) (Tm f v) (Formula f v) (Formula f v)
  deriving (Eq, Ord, Show)

data Sense = Lesser | Greater deriving (Eq, Ord, Show)
instance Pretty Sense where
  pretty Lesser = text "<"
  pretty Greater = text ">"

instance (PrettyTerm f, Pretty v) => Pretty (Formula f v) where
  prettyPrec _ FTrue = text "true"
  prettyPrec _ FFalse = text "false"
  prettyPrec p (x :&: y) =
    prettyParen (p > 10)
      (hang (prettyPrec 11 x <+> text "&") 2 (prettyPrec 11 y))
  prettyPrec p (x :|: y) =
    prettyParen (p > 10)
      (hang (prettyPrec 11 x <+> text "|") 2 (prettyPrec 11 y))
  prettyPrec p (Size t) = pretty t
  prettyPrec p (HeadIs sense t x) = text "hd(" <> pretty t <> text ")" <+> pretty sense <+> pretty x
  prettyPrec p (Less t u) = pretty t <+> text "<" <+> pretty u
  prettyPrec p (Equal t u FTrue FFalse) =
    pretty t <+> text "=" <+> pretty u
  prettyPrec p (Equal t u x y) =
    prettyPrec p ((Equal t u FTrue FFalse :&: x) :|: y)

instance (Sized f, Ord v) => Symbolic (Formula f v) where
  type ConstantOf (Formula f v) = f
  type VariableOf (Formula f v) = v
  termsDL FTrue = mzero
  termsDL FFalse = mzero
  termsDL (p :&: q) = termsDL p `mplus` termsDL q
  termsDL (p :|: q) = termsDL p `mplus` termsDL q
  termsDL (Size t) = msum (map (return . Var) (Map.keys (FM.vars (bound t))))
  termsDL (HeadIs _ t _) = return t
  termsDL (Less t u) = return t `mplus` return u
  termsDL (Equal t u p q) = return t `mplus` return u `mplus` termsDL p `mplus` termsDL q

  substf sub FTrue = FTrue
  substf sub FFalse = FFalse
  substf sub (p :&: q) = substf sub p &&& substf sub q
  substf sub (p :|: q) = substf sub p ||| substf sub q
  substf sub (Size t) = Size t { bound = substFM sub (bound t) }
    where
      substFM f t =
        constTerm (FM.constant t) +
        sum [k ^* termSize (f v) | (v, k) <- Map.toList (FM.vars t)]
  substf sub (HeadIs sense t f) = HeadIs sense (substf sub t) f
  substf sub (Less t u) = Less (substf sub t) (substf sub u)
  substf sub (Equal t u p q) = Equal (substf sub t) (substf sub u) (substf sub p) (substf sub q)

termSize :: (Sized f, Ord v) => Tm f v -> FM.Term v
termSize = foldTerm FM.var fun
  where
    fun f ss = constTerm (funSize f) + sum ss

sizeAxioms :: Ord v => Bound (FM.Term v) -> [Bound (FM.Term v)]
sizeAxioms s = [ var x >== 1 | x <- Map.keys (FM.vars (bound s)) ]

termAxioms :: (Symbolic a, Ord (VariableOf a)) => a -> [Bound (FM.Term (VariableOf a))]
termAxioms t = [ var x >== 1 | x <- usort (vars t) ]

(|||), (&&&) :: Formula f v -> Formula f v -> Formula f v
FTrue ||| _ = FTrue
_ ||| FTrue = FTrue
FFalse ||| p = p
p ||| FFalse = p
Equal t u p q ||| r = Equal t u p (q ||| r)
r ||| Equal t u p q = Equal t u p (q ||| r)
p ||| q = p :|: q

FTrue &&& p = p
p &&& FTrue = p
FFalse &&& p = FFalse
p &&& FFalse = FFalse
Equal t u p q &&& r = Equal t u (p &&& r) (q &&& r)
r &&& Equal t u p q = Equal t u (p &&& r) (q &&& r)
p &&& (q :|: r) = (p &&& q) ||| (p &&& r)
(p :|: q) &&& r = (p &&& r) ||| (q &&& r)
p &&& q = p :&: q

true :: (Sized f, Ord f, Ord v) => Formula f v -> Bool
true FTrue = True
true FFalse = False
true (p :&: q) = true p && true q
true (p :|: q) = true p || true q
true (Less t u) = t `simplerThan` u
true _ = ERROR "can't check truth of split constraints"

type M = State Int

runM :: (Symbolic a, Numbered (VariableOf a)) => (a -> M b) -> a -> b
runM f x = evalState (f x) n
  where
    n = maximum (0:map (succ . number) (vars x))

newName :: Numbered a => a -> M a
newName x = do
  n <- get
  put $! n+1
  return (withNumber n x)

simplify :: (Sized f, Ord f, Ord v, Numbered v) => Formula f v -> M (Formula f v)
simplify FTrue = return FTrue
simplify FFalse = return FFalse
simplify (p :&: q) = liftM2 (&&&) (simplify p) (simplify q)
simplify (p :|: q) = liftM2 (|||) (simplify p) (simplify q)
simplify (Equal t u p q) | t == u = simplify (p ||| q)
simplify (Equal t u p q) =
  case unify t u of
    Nothing -> simplify q
    Just{} -> liftM2 (equal t u) (simplify p) (simplify q)
  where
    equal t u FFalse q = q
    equal t u _ FTrue = FTrue
    equal t u p q = Equal t u p q
simplify (Size s)
  | isNothing (solve s) = return FFalse
  | isNothing (solve (negateBound s)) = return FTrue
  where
    solve s = FM.solve (addTerms [s] p)
    p = problem (sizeAxioms s)
simplify (HeadIs sense (Fun f ts) g)
  | test sense f g = return FTrue
  | otherwise = return FFalse
  where
    test Lesser = (<)
    test Greater = (>)
simplify (HeadIs Greater _ f) | funSize f == 0 && funArity f == 1 =
  return FFalse
simplify (Less t u) | t == u = return FFalse
simplify (Less t (Var x)) | x `elem` vars t = return FFalse
simplify (Less (Var x) t) | x `elem` vars t = return FTrue
simplify (Less t u) | isFun t || isFun u = do
  rest <- structLess t u
  simplify (Size (sz </= 0) ||| (Size (sz >== 0) &&& Size (sz <== 0) &&& rest))
  where
    sz = termSize t - termSize u
simplify p = return p

structLess :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> M (Formula f v)
structLess (Fun f ts) (Fun g us) =
  return $
  case compare f g of
    LT -> FTrue
    GT -> FFalse
    EQ -> loop ts us
  where
    loop [] [] = FFalse
    loop (t:ts) (u:us) = Equal t u (loop ts us) (Less t u)
structLess (Var x) (Fun f ts) = do
  u <- specialise x f
  rest <- structLess u (Fun f ts)
  return $
    Equal (Var x) u rest $
      HeadIs Lesser (Var x) f
structLess (Fun f ts) (Var x) = do
  u <- specialise x f
  rest <- structLess (Fun f ts) u
  return $
    Equal (Var x) u rest $
      HeadIs Greater (Var x) f

specialise :: (Sized f, Ord f, Ord v, Numbered v) => v -> f -> M (Tm f v)
specialise x f = do
  ns <- replicateM (funArity f) (newName x)
  return (Fun f (map Var ns))

negFormula :: (Sized f, Numbered v, Ord f, Ord v) => Formula f v -> M (Formula f v)
negFormula FTrue = return FFalse
negFormula FFalse = return FTrue
negFormula (p :&: q) = liftM2 (|||) (negFormula p) (negFormula q)
negFormula (p :|: q) = liftM2 (&&&) (negFormula p) (negFormula q)
negFormula (Size s) = return (Size (negateBound s))
negFormula (Less t u) = return (Equal t u FTrue (Less u t))
negFormula (HeadIs sense (Var x) f) = do
  t <- specialise x f
  return (Equal (Var x) t FTrue (HeadIs (negateSense sense) (Var x) f))
  where
    negateSense Lesser = Greater
    negateSense Greater = Lesser
negFormula _ = ERROR "must call split before using a context"

-- Solved formulas.
type SolvedOf a = Solved (ConstantOf a) (VariableOf a)
data Solved f v =
  -- We complete the set of constraints as follows:
  -- * Less is transitively closed.
  -- * If Less x y, then size x <= size y.
  -- * If HeadGreater x f and Less x y and HeadLess y g with g <= f,
  --   then size x < size y (size x = size y implies f < g).
  --   When x = y this becomes: if HeadGreater x f and HeadLess x f,
  --   then size x < size x, i.e. false.
  -- Once completed, the constraints are satisfiable iff:
  -- 1. The size constraints are satisfiable.
  -- 2. There is no literal Less x x.
  Unsolvable |
  Tautological |
  Solved {
    -- Size constraints.
    prob        :: Problem v,
    solution    :: Map v Rational,
    -- HeadLess and HeadGreater constraints for variables.
    headLess    :: Map v f,
    headGreater :: Map v f,
    -- Less x y constraints. Transitively closed.
    less        :: Map v (Set v) }
  deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Solved f v) where
  pretty Unsolvable = text "false"
  pretty Tautological = text "true"
  pretty x =
    pretty [
      pretty (prob x),
      pretty (solution x),
      pretty (headLess x),
      pretty (headGreater x),
      pretty (less x) ]

solve :: (Sized f, Ord f, Ord v) => Formula f v -> Solved f v
solve = solve1 . filter (/= FTrue) . literals
  where
    literals (p :&: q) = literals p ++ literals q
    literals (p :|: q) = ERROR "must call split before using a context"
    literals (Equal _ _ _ _) = ERROR "must call split before using a context"
    literals p = [p]

solve1 :: (Sized f, Ord f, Ord v) => [Formula f v] -> Solved f v
solve1 [] = Tautological
solve1 ls
  | not (null equal) = ERROR "must call split before using a context"
  | FFalse `elem` ls = Unsolvable
  | or [ Set.member x s | (x, s) <- Map.toList less' ] = Unsolvable
  | otherwise =
      case FM.solve prob of
        Nothing -> Unsolvable
        Just sol -> Solved prob sol headLess' headGreater' less'
  where
    size = [s | Size s <- ls]
    headLess = [(unVar x, f) | HeadIs Lesser x f <- ls]
    headGreater = [(unVar x, f) | HeadIs Greater x f <- ls]
    headLess' = Map.fromListWith min headLess
    headGreater' = Map.fromListWith max headGreater
    less = [(unVar t, unVar u) | Less t u <- ls]
    less' = close less
    equal = [() | Equal{} <- ls]
    unVar (Var x) = x
    unVar _ = ERROR "must call split before using a context"
    prob = FM.problem (size ++ termAxioms ls ++ lessProb ++ headProb)
    lessProb = [var x <== var y | (x, y) <- less]
    headProb = [var x </= var y | (x, f) <- Map.toList headGreater', (y, g) <- Map.toList headLess', f >= g]

close :: Ord a => [(a, a)] -> Map a (Set a)
close bs = Map.fromList [(x, close1 bs x) | x <- usort (map fst bs)]

close1 :: Ord a => [(a, a)] -> a -> Set a
close1 bs x = aux (successors x) Set.empty
  where
    aux [] s = s
    aux (x:xs) s
      | x `Set.member` s = aux xs s
      | otherwise = aux (successors x ++ xs) (Set.insert x s)
      where
    successors x = [y | (x', y) <- bs, x == x']

satisfiable :: (Ord f, Ord v) => Solved f v -> Bool
satisfiable Unsolvable = False
satisfiable _ = True

modelSize :: (Pretty v, Sized f, Ord f, Ord v) => Tm f v -> Solved f v -> Integer
modelSize t Unsolvable = __
modelSize t Tautological = fromIntegral (size t)
modelSize t s = ceiling (FM.eval 1 (solution s) (termSize t))

minimiseContext :: (Pretty v, Ord f, Ord v) => FM.Term v -> Context f v -> Context f v
minimiseContext t ctx =
  ctx { solved = s, model = toModel s }
  where
    s = minimiseSolved t (solved ctx)

minimiseSolved :: (Pretty v, Ord v) => FM.Term v -> Solved f v -> Solved f v
minimiseSolved t Unsolvable = __
minimiseSolved t Tautological = Tautological
minimiseSolved t s =
  s { solution = loop (solution s) }
  where
    loop m
      | x < 0 = __
      | otherwise =
          case FM.solve (addTerms [t <== fromIntegral (n-1)] (prob s)) of
            Nothing -> m
            Just m -> loop m
      where
        x = FM.eval 1 m t
        n = ceiling x

data Extended f v =
    Original f
    -- ConstrainedVar x n k (Just f):
    -- x is at position n among all ConstrainedVars,
    -- has size k and its head is smaller than f
  | ConstrainedVar v Int Rational (Maybe f)
  deriving (Eq, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Extended f v) where
  pretty (Original f) = pretty f
  pretty (ConstrainedVar x n k l) =
    text "c" <> pretty n <> pretty x <> brackets (pretty k <> bound l)
    where
      bound Nothing = text ""
      bound (Just f) = text ", >" <+> pretty f

instance (PrettyTerm f, Pretty v) => PrettyTerm (Extended f v) where
  termStyle (Original f) = termStyle f
  termStyle ConstrainedVar{} = Curried

toModel :: (Ord f, Ord v) => Solved f v -> Map v (Extended f v)
toModel Unsolvable = __
toModel Tautological = Map.empty
toModel s =
  Map.fromList [(x, var x i) | (x, i) <- zip (sortBy cmp vs) [0..]]
  where
    vs = usort (Set.toList (pvars (prob s)) ++
                Map.keys (headLess s) ++
                Map.keys (headGreater s) ++
                concat [(x:Set.toList s) | (x, s) <- Map.toList (less s)])
    cmp x y
      | y `Set.member` Map.findWithDefault Set.empty x (less s) = LT
      | x `Set.member` Map.findWithDefault Set.empty y (less s) = GT
      | otherwise = compare x y
    var x i =
      ConstrainedVar x i
        (varSize x)
        (try minimum
         (catMaybes
          [ Map.lookup y (headLess s)
          | y <- x:filter (sameSize x) (Set.toList (Map.findWithDefault Set.empty x (less s))) ]))
    varSize x = Map.findWithDefault 1 x (solution s)
    sameSize x y = varSize x == varSize y
    try f [] = Nothing
    try f xs = Just (f xs)
