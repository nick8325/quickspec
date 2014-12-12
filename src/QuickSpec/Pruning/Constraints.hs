{-# LANGUAGE TypeOperators, TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, ConstraintKinds #-}
module QuickSpec.Pruning.Constraints where

#include "errors.h"
import QuickSpec.Base
import qualified QuickSpec.Pruning.FourierMotzkin as FM
import QuickSpec.Pruning.FourierMotzkin hiding (Term(..), trace, Stop, solve)
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
  pretty (Constrained (Context { formula = Disj [Conj []] }) x) = pretty x
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
type ClauseOf a  = Clause  (ConstantOf a) (VariableOf a)
newtype Formula f v = Disj { disjuncts :: [Clause f v] }  deriving (Eq, Ord, Show)
newtype Clause f v  = Conj { conjuncts :: [Literal f v] } deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Formula f v) where
  pretty (Disj []) = text "false"
  pretty (Disj [x]) = pretty x
  pretty (Disj ls) =
    fsep (punctuate (text " |") (map pretty ls))

instance (PrettyTerm f, Pretty v) => Pretty (Clause f v) where
  pretty (Conj []) = text "true"
  pretty (Conj [x]) = pretty x
  pretty (Conj ls) =
    fsep (punctuate (text " &") (map pretty ls))

instance (Sized f, Ord v) => Symbolic (Formula f v) where
  type ConstantOf (Formula f v) = f
  type VariableOf (Formula f v) = v
  termsDL (Disj fs) = msum (map termsDL fs)
  substf sub (Disj fs) = Disj (map (substf sub) fs)

instance (Sized f, Ord v) => Symbolic (Clause f v) where
  type ConstantOf (Clause f v) = f
  type VariableOf (Clause f v) = v
  termsDL (Conj fs) = msum (map termsDL fs)
  substf sub (Conj fs) = Conj (map (substf sub) fs)

type LiteralOf a = Literal (ConstantOf a) (VariableOf a)
data Literal f v =
  -- After calling split, literals are in the following form:
  -- * No occurrences of Equal.
  -- * HeadLess, HeadGreater and Less can only be applied to variables.
  -- * No tautological or impossible literals.
    Size (Bound (FM.Term v))
  | HeadLess (Tm f v) (Arity f)
  | HeadGreater (Tm f v) (Arity f)
  | Less (Tm f v) (Tm f v)
  | Equal (Tm f v) (Tm f v)
  deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Literal f v) where
  pretty (Size t) = pretty t
  pretty (HeadLess t x) = text "hd(" <> pretty t <> text ") <" <+> pretty x
  pretty (HeadGreater t x) = text "hd(" <> pretty t <> text ") >" <+> pretty x
  pretty (Less t u) = pretty t <+> text "<" <+> pretty u
  pretty (Equal t u) = pretty t <+> text "=" <+> pretty u

instance (Sized f, Ord v) => Symbolic (Literal f v) where
  type ConstantOf (Literal f v) = f
  type VariableOf (Literal f v) = v

  termsDL (Size t) = msum (map (return . Var) (Map.keys (FM.vars (bound t))))
  termsDL (HeadLess t _) = termsDL t
  termsDL (HeadGreater t _) = termsDL t
  termsDL (Less t u) = termsDL t `mplus` termsDL u
  termsDL (Equal t u) = termsDL t `mplus` termsDL u

  substf sub (Size t) = Size t { bound = substFM sub (bound t) }
  substf sub (HeadLess t f) = HeadLess (substf sub t) f
  substf sub (HeadGreater t f) = HeadGreater (substf sub t) f
  substf sub (Less t u) = Less (substf sub t) (substf sub u)
  substf sub (Equal t u) = Equal (substf sub t) (substf sub u)

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

literal :: Literal f v -> Formula f v
literal l = literals [l]

literals :: [Literal f v] -> Formula f v
literals ls = Disj [Conj ls]

disj, conj :: [Formula f v] -> Formula f v
disj fs = Disj (concatMap disjuncts fs)
conj [] = Disj [Conj []]
conj (Disj cs:fs) =
  Disj [ Conj (ls ++ ls') | Conj ls <- cs, Conj ls' <- disjuncts (conj fs) ]

true, false :: Formula f v
true = conj []
false = disj []

neg :: (Sized f, Numbered v, Ord f, Ord v) => Formula f v -> Formula f v
neg (Disj cs) = conj (map negClause cs)
  where
    negClause (Conj ls) = disj (runM (mapM negLiteral) ls)
    negLiteral (Size s) = return $ literal (Size (negateBound s))
    negLiteral (Less t u) = return $ disj (map literal [Equal t u, Less u t])
    negLiteral (HeadLess (Var x) f) = do
      t <- specialise x f
      return . disj . map literal $ [HeadGreater (Var x) f, Equal (Var x) t]
    negLiteral (HeadGreater (Var x) f) = do
      t <- specialise x f
      return . disj . map literal $ [HeadLess (Var x) f, Equal (Var x) t]
    negLiteral _ = ERROR "must call split before using a context"

bool :: Bool -> Formula f v
bool True = true
bool False = false

simplify :: (Sized f, Ord f, Ord v, Numbered v) => Context f v -> Context f v
simplify ctx = toContext (simplifyFormula (formula ctx))
  where
    simplifyFormula (Disj cs) = Disj (prune [] cs)
    prune xs [] = reverse xs
    prune xs (y:ys)
      | any (redundant y) (xs ++ ys) = prune xs ys
      | otherwise = prune (y:xs) ys
    redundant c _ | isNothing (solve1 c) = True
    redundant (Conj ls) c =
      case solve1 c of
        Nothing -> False
        Just s -> all (impliesLiteral s) ls

split :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> (Constrained a, [Constrained a])
split (Constrained ctx x) = (Constrained (toContext ctx') x, concatMap (split' . f) xs)
  where
    (ctx', xs) = splitFormula (formula ctx)
    f (sub, ctx') = substf (evalSubst sub) (Constrained (toContext ctx') x)

split' :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> [Constrained a]
split' x
  | satisfiable (solved (context y)) = y:xs
  | otherwise = xs
  where (y, xs) = split x

type Split f v = (Formula f v, [(Subst f v, Formula f v)])

splitFormula :: (Sized f, Ord f, Ord v, Numbered v) => Formula f v -> Split f v
splitFormula (Disj cs) = (disj (map fst xs), concatMap snd xs)
  where xs = map splitClause cs

splitClause :: (Sized f, Ord f, Ord v, Numbered v) => Clause f v -> Split f v
splitClause (Conj ls) =
  case runM simplifyLiterals ls of
    Stop -> (literals ls, [])
    Substitute sub -> (false, [(sub, literals ls)])
    Simplify ctx -> splitFormula ctx

data Result f v = Substitute (Subst f v) | Simplify (Formula f v) | Stop

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

simplifyLiterals :: (Sized f, Ord f, Ord v, Numbered v) => [Literal f v] -> M (Result f v)
simplifyLiterals [] = return Stop
simplifyLiterals (Equal t u:ls) | t == u = fmap f (simplifyLiterals ls)
  where
    f Stop = Simplify (literals ls)
    f res  = res
simplifyLiterals (Equal t u:ls) =
  return $
  case unify t u of
    Nothing -> Simplify false
    Just sub -> Substitute sub
simplifyLiterals (l:ls) =
  liftM2 op (simplifyLiteral l) (simplifyLiterals ls)
  where
    op Nothing    (Simplify ctx)  = Simplify (conj [literal l, ctx])
    op (Just ctx) (Simplify ctx') = Simplify (conj [ctx, ctx'])
    op (Just ctx) Stop            = Simplify (conj [ctx, literals ls])
    op _          res             = res

simplifyLiteral :: (Sized f, Ord f, Ord v, Numbered v) => Literal f v -> M (Maybe (Formula f v))
simplifyLiteral (Size s)
  | isNothing (solveSize s) = return (Just false)
  | isNothing (solveSize (negateBound s)) = return (Just true)
simplifyLiteral (HeadLess (Fun f ts) g) =
  return (Just (bool (f :/: length ts < g)))
simplifyLiteral (HeadGreater (Fun f ts) g) =
  return (Just (bool (f :/: length ts > g)))
simplifyLiteral (HeadGreater _ (f :/: 1)) | funSize f == 0 =
  return (Just false)
simplifyLiteral (Less t u) | t == u = return (Just false)
simplifyLiteral (Less t (Var x)) | x `elem` vars t = return (Just false)
simplifyLiteral (Less (Var x) t) | x `elem` vars t = return (Just true)
simplifyLiteral (Less t u) | isFun t || isFun u = do
  rest <- structLess t u
  return . Just $
    conj [
      literal (Size (sz <== 0)),
      disj [
        literal (Size (sz </= 0)),
        rest]]
  where
    sz = termSize t - termSize u
simplifyLiteral l = return Nothing

structLess :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> M (Formula f v)
structLess (Fun f ts) (Fun g us) =
  return $
  case compare (f :/: length ts) (g :/: length us) of
    LT -> true
    GT -> false
    EQ -> argsLess ts us
structLess (Var x) (Fun f ts) = do
  u <- specialise x (f :/: length ts)
  rest <- structLess u (Fun f ts)
  return $
    disj [
      literal (HeadLess (Var x) (f :/: length ts)),
      conj [literal (Equal (Var x) u), rest]]
structLess (Fun f ts) (Var x) = do
  u <- specialise x (f :/: length ts)
  rest <- structLess (Fun f ts) u
  return $
    disj [
      literal (HeadGreater (Var x) (f :/: length ts)),
      conj [literal (Equal (Var x) u), rest]]

specialise :: (Sized f, Ord f, Ord v, Numbered v) => v -> Arity f -> M (Tm f v)
specialise x (f :/: n) = do
  ns <- replicateM n (newName x)
  return (Fun f (map Var ns))

argsLess :: (Sized f, Ord f, Ord v) => [Tm f v] -> [Tm f v] -> Formula f v
argsLess [] [] = false
argsLess (t:ts) (u:us) =
  disj [
    literal (Less t u),
    conj [literal (Equal t u), argsLess ts us]]

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

solve :: (Sized f, Ord f, Ord v) => Formula f v -> Solved f v
solve (Disj cs) =
  Solved (Set.fromList (catMaybes (map solve1 cs)))

solve1 :: (Sized f, Ord f, Ord v) => Clause f v -> Maybe (Solved1 f v)
solve1 (Conj ls)
  | not (null equal) = ERROR "must call split before using a context"
  | isNothing (FM.solve prob) = Nothing
  | or [ Set.member x s | (x, s) <- Map.toList less' ] = Nothing
  | otherwise = Just (Solved1 prob headLess' headGreater' less')
  where
    size = [s | Size s <- ls]
    headLess = [(unVar x, f) | HeadLess x f <- ls]
    headGreater = [(unVar x, f) | HeadGreater x f <- ls]
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

implies :: (Sized f, Numbered v, Ord f, Ord v) => Solved f v -> Context f v -> Bool
implies form ctx = any (impliesClause form) cs
  where
    (Disj cs, _) = splitFormula (formula ctx)

impliesClause :: (Sized f, Numbered v, Ord f, Ord v) => Solved f v -> Clause f v -> Bool
impliesClause (Solved fs) (Conj ls) =
  and [ or [ impliesLiteral f l | f <- Set.toList fs ] | l <- ls ]

impliesLiteral :: (Sized f, Numbered v, Ord f, Ord v) => Solved1 f v -> Literal f v -> Bool
impliesLiteral form (Size s) =
  isNothing (FM.solve (addTerms ts (prob form)))
  where
    ts = negateBound s:sizeAxioms s
impliesLiteral form (Less (Var x) (Var y)) =
  y `Set.member` Map.findWithDefault Set.empty x (less form)
impliesLiteral form (HeadLess (Var x) f) =
  case Map.lookup x (headLess form) of
    Just g | g < f -> True
    _ -> False
impliesLiteral form (HeadGreater (Var x) f) =
  case Map.lookup x (headGreater form) of
    Just g | g > f -> True
    _ -> False
impliesLiteral _ _ = ERROR "must call split before using a context"

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
