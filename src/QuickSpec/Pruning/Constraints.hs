{-# LANGUAGE TypeOperators, TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, ConstraintKinds #-}
module QuickSpec.Pruning.Constraints where

#include "errors.h"
import QuickSpec.Base
import qualified QuickSpec.Pruning.FourierMotzkin as FM
import QuickSpec.Pruning.FourierMotzkin hiding (Term(..), trace, Stop, solve, implies)
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
{-
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
t, u :: Tm F PruningVariable
-- t = Fun (F "sx") []
-- u = Fun Ty [t]
--t = Fun (F "+") [Var 0, Var 1]
--u = Fun (F "+") [Var 1, Var 0]
(t, u) = (f (Var 0) (Var 1), f (Var 1) (Var 0))
  where
    f x y = Fun (F "*") [x, Fun (F "+") [y, Fun (F "+") [y, y]]]
r1 = Constrained (toContext (literal (Less u t))) (Rule t u)
r2 = Constrained (toContext (literal (Less t u))) (Rule u t)
-}
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

type ContextOf a = Context (ConstantOf a) (VariableOf a)
data Context f v =
  Context {
    formula :: Formula f v,
    solved  :: Solved f v }
  deriving Show

toContext :: (Sized f, Ord f, Ord v) => Formula f v -> Context f v
toContext x = Context x (solve x)

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
  | HeadIs Sense (Tm f v) (Arity f)
  | Less (Tm f v) (Tm f v)
    -- Equal t u p q represents (t = u & p) | q.
    -- The smart constructors disj and conj lift
    -- Equal to the top level.
  | Equal (Tm f v) (Tm f v) (Formula f v) (Formula f v)
  deriving (Eq, Ord, Show)

data Sense = Lesser | Greater deriving (Eq, Ord, Show)
instance Pretty Sense where
  pretty Lesser = text "<"
  pretty Greater = text ">"

negateSense :: Sense -> Sense
negateSense Lesser = Greater
negateSense Greater = Lesser

evalSense :: Ord a => Sense -> a -> a -> Bool
evalSense Lesser = (<)
evalSense Greater = (>)

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
  prettyPrec p (Equal t u x y) =
    prettyParen (p > 10) $
    hang
      (parens
        (pretty t <+> text "=" <+> pretty u <+> text "&" <+> prettyPrec 11 x) <+> text "|") 2
      (prettyPrec 11 y)

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
  substf sub (HeadIs sense t f) = HeadIs sense (substf sub t) f
  substf sub (Less t u) = Less (substf sub t) (substf sub u)
  substf sub (Equal t u p q) = Equal (substf sub t) (substf sub u) (substf sub p) (substf sub q)

substFM :: (Sized f, Ord v') => (v -> Tm f v') -> FM.Term v -> FM.Term v'
substFM f t =
  constTerm (FM.constant t) +
  sum [k ^* termSize (f v) | (v, k) <- Map.toList (FM.vars t)]

termSize :: (Sized f, Ord v) => Tm f v -> FM.Term v
termSize = foldTerm FM.var fun
  where
    fun f ss = fromIntegral (funSize f) + sum ss

sizeAxioms :: Ord v => Bound (FM.Term v) -> [Bound (FM.Term v)]
sizeAxioms s = [ var x >== 1 | x <- Map.keys (FM.vars (bound s)) ]

termAxioms :: (Symbolic a, Ord (VariableOf a)) => a -> [Bound (FM.Term (VariableOf a))]
termAxioms t = [ var x >== 1 | x <- usort (vars t) ]

solveSize :: Ord v => Bound (FM.Term v) -> Maybe (Map v Rational)
solveSize s =
  FM.solve (problem (s:sizeAxioms s))

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
p &&& q = p :&: q

neg :: (Sized f, Numbered v, Ord f, Ord v) => Formula f v -> M (Formula f v)
neg FTrue = return FFalse
neg FFalse = return FTrue
neg (p :&: q) = liftM2 (&&&) (neg p) (neg q)
neg (p :|: q) = liftM2 (|||) (neg p) (neg q)
neg (Size s) = return (Size (negateBound s))
neg (Less t u) = return (Equal t u FTrue (Less u t))
neg (HeadIs sense (Var x) f) = do
  t <- specialise x f
  return (Equal (Var x) t FTrue (HeadIs (negateSense sense) (Var x) f))
neg _ = ERROR "must call split before using a context"

bool :: Bool -> Formula f v
bool True = FTrue
bool False = FFalse

split :: (Symbolic a, Ord a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> (Constrained a, [Constrained a])
split (Constrained ctx x) = (make form, concatMap split' zs)
  where
    make ctx = Constrained (toContext ctx) x
    (form, xs) = splitFormula (runM simplify (formula ctx))
    ys = collate (foldr (|||) FFalse) xs
    zs = [ substf (evalSubst sub) (make form) | (sub, form) <- ys ]

split' :: (Symbolic a, Ord a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> [Constrained a]
split' x
  | satisfiable (solved (context y)) = y:xs
  | otherwise = xs
  where (y, xs) = split x

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

splitFormula :: (Sized f, Ord f, Ord v, Numbered v) => Formula f v -> (Formula f v, [(Subst f v, Formula f v)])
splitFormula (Equal t u p q) = (q', (sub, p):xs)
  where
    Just sub = unify t u
    (q', xs) = splitFormula q
splitFormula p = (p, [])

simplify :: (Sized f, Ord f, Ord v, Numbered v) => Formula f v -> M (Formula f v)
simplify FTrue = return FTrue
simplify FFalse = return FFalse
simplify (p :&: q) = liftM2 (&&&) (simplify p) (simplify q)
simplify (p :|: q) = liftM2 (|||) (simplify p) (simplify q)
simplify (Equal t u p q) | t == u = simplify (p ||| q)
simplify (Equal t u p q) =
  case unify t u of
    Nothing -> simplify q
    Just{} -> fmap (Equal t u p) (simplify q)
simplify (Size s)
  | isNothing (solveSize s) = return FFalse
  | isNothing (solveSize (negateBound s)) = return FTrue
simplify (HeadIs sense (Fun f ts) g) =
  return (bool (evalSense sense (f :/: length ts) g))
simplify (HeadIs Greater _ (f :/: 1)) | funSize f == 0 =
  return FFalse
simplify (Less t u) | t == u = return FFalse
simplify (Less t (Var x)) | x `elem` vars t = return FFalse
simplify (Less (Var x) t) | x `elem` vars t = return FTrue
simplify (Less t u) | isFun t || isFun u = do
  rest <- structLess t u
  simplify (Size (sz <== 0) &&& (Size (sz </= 0) ||| rest))
  where
    sz = termSize t - termSize u
simplify p = return p

structLess :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> M (Formula f v)
structLess (Fun f ts) (Fun g us) =
  return $
  case compare (f :/: length ts) (g :/: length us) of
    LT -> FTrue
    GT -> FFalse
    EQ -> argsLess ts us
structLess (Var x) (Fun f ts) = do
  u <- specialise x (f :/: length ts)
  rest <- structLess u (Fun f ts)
  return $
    Equal (Var x) u rest $
      HeadIs Lesser (Var x) (f :/: length ts)
structLess (Fun f ts) (Var x) = do
  u <- specialise x (f :/: length ts)
  rest <- structLess (Fun f ts) u
  return $
    Equal (Var x) u rest $
      HeadIs Greater (Var x) (f :/: length ts)

specialise :: (Sized f, Ord f, Ord v, Numbered v) => v -> Arity f -> M (Tm f v)
specialise x (f :/: n) = do
  ns <- replicateM n (newName x)
  return (Fun f (map Var ns))

argsLess :: (Sized f, Ord f, Ord v) => [Tm f v] -> [Tm f v] -> Formula f v
argsLess [] [] = FFalse
argsLess (t:ts) (u:us) =
  Equal t u (argsLess ts us) (Less t u)

type SolvedOf a = Solved (ConstantOf a) (VariableOf a)
newtype Solved f v =
  Solved {
    clauses :: Set (Solved1 f v) }
  deriving (Eq, Ord, Show)
data Solved1 f v =
  -- We complete the set of constraints as follows:
  -- * Less is transitively closed.
  -- * If Less x y, then size x <= size y.
  -- * If HeadGreater x f and Less x y and HeadLess y f,
  --   then size x < size y (size x = size y implies f < f).
  --   When x = y this becomes: if HeadGreater x f and HeadLess x f,
  --   then size x < size x, i.e. false.
  -- Once completed, the constraints are satisfiable iff:
  -- 1. The size constrains are satisfiable.
  -- 2. There is no literal Less x x.
  Solved1 {
    -- Size constraints.
    prob        :: Problem v,
    -- HeadLess and HeadGreater constraints for variables.
    headLess    :: Map v (Arity f),
    headGreater :: Map v (Arity f),
    -- Less x y constraints. Transitively closed.
    less        :: Map v (Set v) }
  deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Solved f v) where
  pretty (Solved cs) =
    case Set.toList cs of
      [] -> text "false"
      [c] -> pretty c
      cs -> fsep (punctuate (text " |") (map pretty cs))

instance (PrettyTerm f, Pretty v) => Pretty (Solved1 f v) where
  pretty x =
    pretty [
      pretty (prob x),
      pretty (headLess x),
      pretty (headGreater x),
      pretty (less x) ]

flatten :: Formula f v -> [[Formula f v]]
flatten FTrue = [[]]
flatten FFalse = []
flatten (p :&: q) = liftM2 (++) (flatten p) (flatten q)
flatten (p :|: q) = flatten p ++ flatten q
flatten t = [[t]]

solve :: (Sized f, Ord f, Ord v) => Formula f v -> Solved f v
solve f =
  Solved (Set.fromList (catMaybes (map solve1 (flatten f))))

solve1 :: (Sized f, Ord f, Ord v) => [Formula f v] -> Maybe (Solved1 f v)
solve1 [] = Just unconditionalSolved1
solve1 ls
  | not (null equal) = ERROR "must call split before using a context"
  | isNothing (FM.solve prob) = Nothing
  | or [ Set.member x s | (x, s) <- Map.toList less' ] = Nothing
  | otherwise = Just (Solved1 prob headLess' headGreater' less')
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

-- XXX check if this helps with performance
unconditionalSolved1 :: Solved1 f v
unconditionalSolved1 = Solved1 FM.empty Map.empty Map.empty Map.empty

close :: Ord a => [(a, a)] -> Map a (Set a)
close bs = Map.fromList [(x, close1 bs x) | x <- usort (map fst bs)]

close1 :: Ord a => [(a, a)] -> a -> Set a
close1 bs x = aux [x] Set.empty
  where
    aux [] s = s
    aux (x:xs) s
      | x `Set.member` s = aux xs s
      | otherwise = aux (ys ++ xs) (Set.union (Set.fromList ys) s)
      where
        ys = [y | (x', y) <- bs, x == x']

satisfiable :: (Ord f, Ord v) => Solved f v -> Bool
satisfiable (Solved cs) = not (Set.null cs)

implies :: (Sized f, Numbered v, Ord f, Ord v) => Solved f v -> Formula f v -> Bool
implies _ FTrue = True
implies _ FFalse = False
implies s (p :&: q) = implies s p && implies s q
implies s (p :|: q) = implies s p || implies s q
implies (Solved s) l = or [ implies1 f l | f <- Set.toList s ]

implies1 :: (Sized f, Numbered v, Ord f, Ord v) => Solved1 f v -> Formula f v -> Bool
implies1 form (Size s) =
  isNothing (FM.solve (addTerms ts (prob form)))
  where
    ts = negateBound s:sizeAxioms s
implies1 form (Less (Var x) (Var y)) =
  y `Set.member` Map.findWithDefault Set.empty x (less form)
implies1 form (HeadIs Lesser (Var x) f) =
  case Map.lookup x (headLess form) of
    Just g | g < f -> True
    _ -> False
implies1 form (HeadIs Greater (Var x) f) =
  case Map.lookup x (headGreater form) of
    Just g | g > f -> True
    _ -> False
implies1 _ _ = ERROR "must call split before using a context"

minSize :: (Sized f, Numbered v, Ord f, Ord v) => Solved f v -> Tm f v -> Integer
minSize (Solved fs) t = minimum [ minSize1 f t | f <- Set.toList fs ]

minSize1 :: (Sized f, Numbered v, Ord f, Ord v) => Solved1 f v -> Tm f v -> Integer
minSize1 form t = minProbSize (addTerms (termAxioms t) (prob form)) (termSize t)

minProbSize :: Ord v => Problem v -> FM.Term v -> Integer
minProbSize prob t =
  loop (eval (fromMaybe __ (FM.solve prob)) t)
  where
    loop x | x < 0 = __
    loop x =
      case FM.solve (addTerms [t <== fromIntegral (n-1)] prob) of
        Nothing -> n
        Just m -> loop (eval m t)
      where
        n = ceiling x
