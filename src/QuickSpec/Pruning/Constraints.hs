{-# LANGUAGE TypeOperators, TypeFamilies, CPP, FlexibleContexts, UndecidableInstances, StandaloneDeriving #-}
module QuickSpec.Pruning.Constraints where

#include "errors.h"
import QuickSpec.Base
import qualified QuickSpec.Pruning.FourierMotzkin as FM
import QuickSpec.Pruning.FourierMotzkin hiding (Term(..), trace)
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
  pretty (Constrained ctx x)
    | Set.null (literals ctx) = pretty x
    | otherwise = hang (pretty x) 2 (text "when" <+> pretty ctx)

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
  -- Invariants:
  --   * Constraint is always satisfiable,
  --   * No literal is tautological,
  --   * At least one argument to StructLess must be a variable,
  --   * StructLess transitively closed apart from above restriction
  Context {
    literals  :: Set (Literal f v),
    mustSplit :: Bool }
  deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Context f v) where
  pretty (Context ls _) | Set.null ls = text "true"
  pretty (Context ls _) =
    fsep (punctuate (text " &") (map pretty (Set.toList ls)))

instance (Eq f, Eq v) => Eq (Context f v) where
  x == y = literals x == literals y
instance (Ord f, Ord v) => Ord (Context f v) where
  compare = comparing literals
instance (Sized f, Ord f, Ord v) => Symbolic (Context f v) where
  type ConstantOf (Context f v) = f
  type VariableOf (Context f v) = v
  termsDL (Context ls _) = msum (map termsDL (Set.toList ls))
  substf sub (Context ls _) = Context (Set.map (substf sub) ls) True

contextUnion :: (Ord f, Ord v) => Context f v -> Context f v -> Context f v
contextUnion (Context ls _) (Context ls' _) = Context (Set.union ls ls') True

type LiteralOf a = Literal (ConstantOf a) (VariableOf a)
data Literal f v =
    SizeIs Rel (Size v)
  | StructLess (Tm f v) (Tm f v)
  deriving (Eq, Ord, Show)
data Rel = REQ | RLT | RGE deriving (Eq, Ord, Show)

instance Pretty Rel where
  pretty REQ = text "="
  pretty RLT = text "<"
  pretty RGE = text ">="

evalRel :: Rel -> T -> T -> [T]
evalRel REQ t u = t === u
evalRel RLT t u = t + 1 <== u
evalRel RGE t u = t >== u

instance (PrettyTerm f, Pretty v) => Pretty (Literal f v) where
  pretty (SizeIs rel s) = pretty s <+> pretty rel <+> text "0"
  pretty (StructLess t u) = pretty t <+> text "<#" <+> pretty u

instance (Sized f, Ord v) => Symbolic (Literal f v) where
  type ConstantOf (Literal f v) = f
  type VariableOf (Literal f v) = v

  termsDL (SizeIs _ (Size cs _)) = msum (map (return . Var) (Map.keys cs))
  termsDL (StructLess t u) = return t `mplus` return u

  substf sub (SizeIs op s) = SizeIs op (substSize sub s)
  substf sub (StructLess t u) = StructLess (substf sub t) (substf sub u)

type ConstraintOf a = Constraint (ConstantOf a) (VariableOf a)
data Constraint f v =
    Less (Tm f v) (Tm f v)
  | Equal (Tm f v) (Tm f v)
  | Literal (Literal f v) deriving Show

instance (Sized f, Ord v) => Symbolic (Constraint f v) where
  type ConstantOf (Constraint f v) = f
  type VariableOf (Constraint f v) = v
  termsDL (Less t u)  = return t `mplus` return u
  termsDL (Equal t u) = return t `mplus` return u
  termsDL (Literal l) = termsDL l
  substf sub (Less t u)  = Less  (substf sub t) (substf sub u)
  substf sub (Equal t u) = Equal (substf sub t) (substf sub u)
  substf sub (Literal l) = Literal (substf sub l)

unconstrained :: a -> Constrained a
unconstrained x = Constrained emptyContext x

emptyContext :: Context f v
emptyContext = Context Set.empty False

add :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => ConstraintOf a -> Constrained a -> [Constrained a]
add c x = runM x (addConstraint c x)

addNegation :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => ContextOf a -> Constrained a -> [Constrained a]
addNegation (Context ls _) x = concatMap (flip addNegatedLiteral x) (Set.toList ls)

addNegatedLiteral :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => LiteralOf a -> Constrained a -> [Constrained a]
addNegatedLiteral (SizeIs RGE s) x = add (Literal (SizeIs RLT s)) x
addNegatedLiteral (SizeIs RLT s) x = add (Literal (SizeIs RGE s)) x
addNegatedLiteral (SizeIs REQ s) x =
  concat [
    add (Literal (SizeIs RLT s)) x,
    add (Literal (SizeIs RGE (s `plus` constSize (-1)))) x]
addNegatedLiteral (StructLess t u) x =
  concat [
    add (Literal (StructLess u t)) x,
    add (Equal t u) x]

split :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> [Constrained a]
split x = runM x (splitConstraint x)

type M = StateT Int []

runM :: (Symbolic a, Numbered (VariableOf a)) => a -> M b -> [b]
runM x m = evalStateT m n
  where
    n = maximum (0:map (succ . number) (vars x))

newName :: Numbered a => a -> M a
newName x = do
  n <- get
  put $! n+1
  return (withNumber n x)

addConstraints :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => [ConstraintOf a] -> Constrained a -> M (Constrained a)
addConstraints [] x = return x
addConstraints (c:cs) x = do
  (y, cs') <- addConstraintWith c x cs
  addConstraints cs' y

addLiterals :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => [LiteralOf a] -> Constrained a -> M (Constrained a)
addLiterals ls x = addConstraints (map Literal ls) x

addConstraint :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => ConstraintOf a -> Constrained a -> M (Constrained a)
addConstraint (Equal t u) x = do
  Just sub <- return (unify t u)
  splitConstraint (substf (evalSubst sub) x)
addConstraint (Less t u) x =
  msum [
    addLiteral (SizeIs RLT sz) x,
    addLiterals [SizeIs REQ sz, StructLess t u] x]
  where
    sz = termSize t `minus` termSize u
addConstraint (Literal l) x = addLiteral l x

addConstraintWith :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a), Symbolic b, ConstantOf a ~ ConstantOf b, VariableOf a ~ VariableOf b) => ConstraintOf a -> Constrained a -> b -> M (Constrained a, b)
addConstraintWith c (Constrained ctx x) y = do
  Constrained ctx' (x', y') <- addConstraint c (Constrained ctx (x, y))
  return (Constrained ctx' x', y')

tautological :: (Sized f, Ord f, Ord v, Numbered v) => Literal f v -> Bool
tautological (SizeIs RLT sz)
  | isNothing (solve (problem (sizeAxioms sz ++ evalRel RGE (encodeSize sz) 0))) = True
tautological (SizeIs RGE sz)
  | isNothing (solve (problem (sizeAxioms sz ++ evalRel RLT (encodeSize sz) 0))) = True
tautological (SizeIs REQ sz)
  | isNothing (solve (problem (sizeAxioms sz ++ evalRel RLT (encodeSize sz) 0))) &&
    isNothing (solve (problem (sizeAxioms sz ++ evalRel RGE (encodeSize sz) 1))) = True
tautological (StructLess t u) | t `simplerThan` u = True
tautological (StructLess (Fun f xs) (Fun g ys))
  | measureFunction f (length xs) < measureFunction g (length ys) = True
tautological _ = False

addLiteral :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => LiteralOf a -> Constrained a -> M (Constrained a)
addLiteral l x | tautological l = return x
addLiteral l x | l `Set.member` literals (context x) = return x
addLiteral l@SizeIs{} c = addBaseLiteral l c
addLiteral l@(StructLess (Fun f _) (Fun g _)) c | f /= g = mzero
addLiteral (StructLess t (Var x)) c | x `elem` vars t = mzero
addLiteral (StructLess (Fun _ xs) (Fun _ ys)) c =
  argsLess xs ys c
addLiteral l@(StructLess t u) c =
  case filter (\l -> l `Set.notMember` ls && not (tautological l)) tc of
    [] -> addLess t u c
    (l':_) ->
      addLiterals [l', l] c
  where
    ls = literals (context c)
    tc = [ StructLess t v | StructLess u' v <- Set.toList ls, u == u', isVar t || isVar v ] ++
         [ StructLess s u | StructLess s t' <- Set.toList ls, t == t', isVar s || isVar u ]

addBaseLiteral :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => LiteralOf a -> Constrained a -> M (Constrained a)
addBaseLiteral l c = do
  let c' = c { context = addLiteralToContext l (context c) }
  guard (satisfiable c')
  return c'

addLess :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => TmOf a -> TmOf a -> Constrained a -> M (Constrained a)
addLess t (Var x) _ | x `elem` vars t = mzero
addLess (Var x) t c | x `elem` vars t = return c
addLess t@(Fun f [_]) u@(Var x) c | funSize f == 0 = do
  y <- newName x
  addConstraints [Equal (Fun f [Var y]) u, Literal (StructLess t u)] c
addLess t@(Var x) u@(Fun f ts) c
  | not (null [ () | StructLess (Fun g _) (Var y) <- Set.toList (literals (context c)), f == g, x == y ]) = do
    us <- sequence [ newName x | _ <- ts ]
    addConstraints [Equal (Var x) (Fun f (map Var us)), Literal (StructLess t u)] c
addLess t@(Fun f ts) u@(Var x) c
  | not (null [ () | StructLess (Var y) (Fun g _) <- Set.toList (literals (context c)), f == g, x == y ]) = do
    us <- sequence [ newName x | _ <- ts ]
    addConstraints [Equal (Fun f (map Var us)) (Var x), Literal (StructLess t u)] c
addLess t u c = addBaseLiteral (StructLess t u) c

addLiteralToContext :: (Sized f, Ord f, Ord v, Numbered v) => Literal f v -> Context f v -> Context f v
addLiteralToContext l (Context ls mustSplit) =
  Context (Set.insert l ls) mustSplit

argsLess :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => [TmOf a] -> [TmOf a] -> Constrained a -> M (Constrained a)
argsLess [] [] _ = mzero
argsLess (x:xs) (y:ys) c =
  msum [
    addConstraint (Less x y) c,
    do { (c', (xs', ys')) <- addConstraintWith (Equal x y) c (xs, ys); argsLess xs' ys' c' } ]

satisfiable :: (Sized (ConstantOf a), Numbered (VariableOf a), Ord (VariableOf a)) => Constrained a -> Bool
satisfiable (Constrained ctx _) =
  isJust (solve (problem (encodeContext ctx)))

encodeContext :: (Ord v, Sized f, Numbered v) => Context f v -> [T]
encodeContext (Context ls False) =
  concat [ sizeVar x >== 1 | x <- usort (vars (Set.toList ls)) ] ++
  concatMap encodeLiteral (Set.toList ls)
encodeContext (Context _ True) = ERROR "must call split after substituting into a constraint"

encodeLiteral :: (Sized f, Numbered v) => Literal f v -> [T]
encodeLiteral (SizeIs op sz)  = evalRel op (encodeSize sz) 0
encodeLiteral StructLess{} = []

splitConstraint :: (Symbolic a, Sized (ConstantOf a), Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a)) => Constrained a -> M (Constrained a)
splitConstraint c@(Constrained (Context _ False) _) = return c
splitConstraint (Constrained (Context ls True) x) = addLiterals (Set.toList ls) (unconstrained x)

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

-- Symbolic sizes of terms.
data Size a =
  Size {
    -- Invariant: no zero coefficients
    coeffs   :: Map a Integer,
    constant :: Integer }
  deriving (Eq, Ord, Show)

instance Pretty a => Pretty (Size a) where
  pretty (Size c 0) | Map.null c = text "0"
  pretty (Size c x) =
    fsep (punctuate (text " +") (f (> 0) id) ++ map (text "-" <+>) (f (< 0) negate))
    where
      f p g =
        [ star (g n) (pretty v) | (v, n) <- Map.toList c, p n ] ++
        [ pretty (g x) | p x ]
      star 1 x = x
      star n x = pretty n <> text "*" <> x

substSize :: (Sized f, Ord v') => (v -> Tm f v') -> Size v -> Size v'
substSize f (Size c x) =
  foldr plus (constSize x)
    [k `times` termSize (f v) | (v, k) <- Map.toList c]

evalSize :: (a -> Integer) -> Size a -> Integer
evalSize f (Size c x) = x + sum [ k * f v | (v, k) <- Map.toList c ]

encodeSize :: Numbered v => Size v -> T
encodeSize (Size c x) =
  foldr (+) (fromIntegral x)
    [fromIntegral k ^* sizeVar v | (v, k) <- Map.toList c]

sizeAxioms :: Numbered v => Size v -> [T]
sizeAxioms (Size c _) =
  concat [ sizeVar v >== 1 | v <- Map.keys c ]

termSize :: (Sized f, Ord v) => Tm f v -> Size v
termSize = foldTerm var fun
  where
    fun f ss = foldr plus (constSize (fromIntegral (funSize f))) ss
    var x    = Size (Map.singleton x 1) 0

constSize :: Integer -> Size a
constSize n = Size Map.empty n

plus :: Ord a => Size a -> Size a -> Size a
plus (Size c x) (Size d y) = Size (Map.filter (/= 0) (Map.unionWith (+) c d)) (x+y)

times :: Ord a => Integer -> Size a -> Size a
times 0 (Size c x) = constSize 0
times n (Size c x) = Size (fmap (* n) c) (n*x)

minus :: Ord a => Size a -> Size a -> Size a
s `minus` s' = s `plus` times (-1) s'

-- Variable assignments for Presburger problem.
sizeVar :: Numbered v => v -> T
sizeVar x = var (sizeNum x)

sizeNum :: Numbered v => v -> Int
sizeNum x = number x*2+1

resultNum :: Int
resultNum = 0

resultVar :: T
resultVar = var resultNum
