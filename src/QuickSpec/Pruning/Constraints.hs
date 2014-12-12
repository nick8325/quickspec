{-# LANGUAGE TypeOperators, TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving, ConstraintKinds #-}
module QuickSpec.Pruning.Constraints where

#include "errors.h"
import QuickSpec.Base
import qualified QuickSpec.Pruning.FourierMotzkin as FM
import QuickSpec.Pruning.FourierMotzkin hiding (Term(..), trace, Stop)
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

import QuickSpec.Pruning
import Data.Rewriting.Rule(Rule(Rule))
data F = F String | Ty deriving (Eq, Ord, Show)
instance Pretty F where
  pretty (F x) = text x
  pretty Ty    = text "@"
instance PrettyTerm F
instance Sized F where
  funSize (F _) = 1
  funSize Ty    = 0
t, u :: Tm F PruningVariable
t = Fun (F "sx") []
u = Fun Ty [t]
r1 = add (Less u t) (unconstrained (Rule t u))
r2 = add (Less t u) (unconstrained (Rule u t))

type T = FM.Term Int

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

toContext :: (Ord f, Ord v) => Formula f v -> Context f v
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
    Size (Bound (FM.Term v))
  | HeadLess (Tm f v) f Int
  | HeadGreater (Tm f v) f Int
  | Less (Tm f v) (Tm f v)
  | Equal (Tm f v) (Tm f v)
  deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Literal f v) where
  pretty (Size t) = pretty t
  pretty (HeadLess t x n) = text "hd(" <> pretty t <> text ") <" <+> pretty x <> text "/" <> pretty n
  pretty (HeadGreater t x n) = text "hd(" <> pretty t <> text ") >" <+> pretty x <> text "/" <> pretty n
  pretty (Less t u) = pretty t <+> text "<" <+> pretty u
  pretty (Equal t u) = pretty t <+> text "=" <+> pretty u

instance (Sized f, Ord v) => Symbolic (Literal f v) where
  type ConstantOf (Literal f v) = f
  type VariableOf (Literal f v) = v

  termsDL (Size t) = msum (map (return . Var) (Map.keys (FM.vars (bound t))))
  termsDL (HeadLess t _ _) = termsDL t
  termsDL (HeadGreater t _ _) = termsDL t
  termsDL (Less t u) = termsDL t `mplus` termsDL u
  termsDL (Equal t u) = termsDL t `mplus` termsDL u

  substf sub (Size t) = Size t { bound = substFM sub (bound t) }
  substf sub (HeadLess t f n) = HeadLess (substf sub t) f n
  substf sub (HeadGreater t f n) = HeadGreater (substf sub t) f n
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

solveSize :: Ord v => Bound (FM.Term v) -> Maybe (Map v Rational)
solveSize s =
  FM.solve (problem (s:[ var x >== 1 | x <- Map.keys (FM.vars (bound s)) ]))

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

bool :: Bool -> Formula f v
bool True = true
bool False = false

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
simplifyLiterals (Equal t u:ls) | t == u = simplifyLiterals ls
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
simplifyLiteral (HeadLess (Fun f ts) g n) =
  return (Just (bool (measureFunction f (length ts) < measureFunction g n)))
simplifyLiteral (HeadGreater (Fun f ts) g n) =
  return (Just (bool (measureFunction f (length ts) > measureFunction g n)))
simplifyLiteral (HeadGreater _ f 1) | funSize f == 0 =
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
  case compare (measureFunction f (length ts)) (measureFunction g (length us)) of
    LT -> true
    GT -> false
    EQ -> argsLess ts us
structLess (Var x) (Fun f ts) = do
  ns <- replicateM (length ts) (newName x)
  let u = Fun f us
      us = map Var ns
  return $
    disj [
      literal (HeadLess (Var x) f (length ts)),
      conj [literal (Equal (Var x) u), argsLess ts us]]
structLess (Fun f ts) (Var x) = do
  ns <- replicateM (length ts) (newName x)
  let u = Fun f us
      us = map Var ns
  return $
    disj [
      literal (HeadGreater (Var x) f (length ts)),
      conj [literal (Equal (Var x) u), argsLess us ts]]

argsLess :: (Sized f, Ord f, Ord v) => [Tm f v] -> [Tm f v] -> Formula f v
argsLess [] [] = false
argsLess (t:ts) (u:us) =
  disj [
    literal (Less t u),
    conj [literal (Equal t u), argsLess ts us]]

type SolvedOf a = Solved (ConstantOf a) (VariableOf a)
data Solved f v = Solved
  deriving Show

solve :: (Ord f, Ord v) => Formula f v -> Solved f v
solve _ = Solved

satisfiable :: (Ord f, Ord v) => Solved f v -> Bool
satisfiable _ = True

{-
implies :: (Sized f, Numbered v, Ord f, Ord v) => Context f v -> Context f v -> Bool
implies ctx (Context ls _) =
  all implies1 (Set.toList ls)
  where
    implies1 (SizeIs REQ sz) =
      unsat (sizeAxioms sz ++ evalRel RGE (encodeSize sz) 1) &&
      unsat (sizeAxioms sz ++ evalRel RLT (encodeSize sz) 0)
    implies1 (SizeIs RGE sz) = unsat (sizeAxioms sz ++ evalRel RLT (encodeSize sz) 0)
    implies1 (SizeIs RLT sz) = unsat (sizeAxioms sz ++ evalRel RGE (encodeSize sz) 0)
    implies1 l | tautological l = True
    implies1 l =
      null (addNegatedLiteral l (Constrained ctx (Fun __ [])))
    unsat p = isNothing (solve' (problem (p ++ encodeContext ctx)))
    --solve' p = traceShow p (traceShowId (solve p))
    solve' = solve

minSize :: (Sized f, Numbered v, Ord v) => Tm f v -> Context f v -> Integer
minSize t ctx =
  loop (sizeIn (fromMaybe __ (solve prob)))
  where
    p    = sizeAxioms sz ++ (encodeSize sz === resultVar)
    sz   = termSize t
    prob = problem (encodeContext ctx ++ p)
    sizeIn m = ceiling (Map.findWithDefault __ resultNum m)
    loop n | n < 0 = __
    loop n =
      case solve' (addTerms (resultVar <== fromIntegral (n-1)) prob) of
        Nothing -> n
        Just m -> loop (sizeIn m)
    --solve' p = traceShow p (traceShowId (solve p))
    solve' p = solve p
-}
