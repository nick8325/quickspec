{-# LANGUAGE TypeOperators, TypeFamilies, CPP #-}
module QuickSpec.Pruning.Constraints where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Utils
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.List
import Data.Maybe
import Data.Integer.SAT hiding (Var)
import qualified Data.Integer.SAT as SAT
import qualified Data.DList as DList
import Control.Monad
import Data.Ord
import Data.Monoid

data Constraint f v = Tm f v :<: Tm f v deriving (Eq, Ord, Show)

substConstraint :: (v -> Tm f v') -> Constraint f v -> Constraint f v'
substConstraint f (t :<: u) = foldTerm f Fun t :<: foldTerm f Fun u

instance Symbolic (Constraint f v) where
  type ConstantOf (Constraint f v) = f
  type VariableOf (Constraint f v) = v
  termsDL (t :<: u) = termsDL t `mplus` termsDL u
  substf sub (t :<: u) = substf sub t :<: substf sub u

instance (PrettyTerm f, Pretty v) => Pretty (Constraint f v) where
  pretty (t :<: u) = hang (pretty t <+> text "<") 2 (pretty u)

less :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> Constraint f v
less t u =
  case focus t u of
    Just (t', u') -> less t' u'
    Nothing -> t :<: u

focus :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> Maybe (Tm f v, Tm f v)
focus t@(Fun _ ts) u@(Fun _ us) =
  case dropWhile (uncurry (==)) (zip ts us) of
    ((t', u'):_) | deciding t' u' -> Just (t', u')
    _ -> Nothing
  where
    deciding t' u' =
      equivalent (flatten (less1 t u)) (flatten (less1 t' u'))
    equivalent p q =
      unsat (Not p :&& q) &&
      unsat (Not q :&& p)
    unsat p = checkSat (assert p noProps) == Nothing
focus _ _ = Nothing

data Constraints f v = Constraints (Set (Constraint f v)) [(Int, Integer)] deriving (Eq, Ord, Show)

instance (PrettyTerm f, Pretty v) => Pretty (Constraints f v) where
  pretty (Constraints cs _) = pretty (Set.toList cs)

constraintsSize :: Constraints f v -> Int
constraintsSize (Constraints cs _) = Set.size cs

noConstraints :: Constraints f v
noConstraints = Constraints Set.empty []

toProp1 :: (Ord f, Sized f, Ord v, Numbered v) => Set (Constraint f v) -> Prop1 f v
toProp1 cs = Conj [ less1 l r | l :<: r <- Set.toList cs ]

add :: (Ord f, Sized f, Ord v, Numbered v) => Constraint f v -> Constraints f v -> Maybe (Constraints f v)
add c (Constraints cs m)
  | c `Set.member` cs = Just (Constraints cs m)
  | otherwise =
    case checkSat (assert (flatten (toProp1 cs')) noProps) of
      Nothing -> Nothing
      Just m -> Just (Constraints cs' m)
  where
    cs' = Set.insert c cs

trySubst :: (Ord f, Sized f, Ord v', Numbered v') => (v -> Tm f v') -> Constraints f v -> Maybe (Constraints f v')
trySubst sub (Constraints cs _) =
  case checkSat (assert (flatten (toProp1 cs')) noProps) of
    Nothing -> Nothing
    Just m -> Just (Constraints cs' m)
  where
    cs' = Set.fromList [ foldTerm sub Fun l `less` foldTerm sub Fun r | l :<: r <- Set.toList cs ]

instance (Ord f, Sized f, Ord v, Numbered v) => Symbolic (Constraints f v) where
  type ConstantOf (Constraints f v) = f
  type VariableOf (Constraints f v) = v
  termsDL (Constraints cs _) = msum (map termsDL (Set.toList cs))
  substf sub cs = fromMaybe __ (trySubst sub cs)

minSize :: (Ord f, Sized f, Ord v, Numbered v) => Constraints f v -> Tm f v -> Integer
minSize (Constraints cs m) t
  | Set.null cs = fromIntegral (size t)
  | otherwise = loop (sizeIn m)
  where
    p = toProp1 cs
    s = termSize t
    sizeIn m = evalSize (\x -> fromMaybe 1 (lookup (sizeNum x) m)) s
    loop n =
      case checkSat (assert (flatten (Conj [SizeIs Positive (constSize n `minus` s), p])) noProps) of
        Nothing -> n
        Just m  -> loop (sizeIn m)

implies :: (Ord f, Sized f, Ord v, Numbered v) => Constraints f v -> Constraint f v -> Bool
implies (Constraints cs _) c@(l :<: r) =
  l /= r && (Set.member c cs || l `simplerThan` r || (unsat c1 && unsat c2))
  where
    unsat p = checkSat (assert (flatten p) noProps) == Nothing
    c1 = Conj [less1 r l, p]
    c2 = Conj [Equal l r, p]
    p = toProp1 cs

data Prop1 f v =
    Conj [Prop1 f v]
  | Disj [Prop1 f v]
  | SizeIs Op (Size (Either f v))
  | Equal (Tm1 f v) (Tm1 f v)
  | Less  (Tm1 f v) (Tm1 f v)
  deriving (Eq, Show)

type Tm1 f v = Tm (F1 f v) v
data F1 f v = Function f | App deriving (Eq, Ord, Show)

toTm1 :: Tm f v -> Tm1 f v
toTm1 (Fun f xs) = Fun App (Function f:map toTm1 xs)
toTm1 t@Var{}    = t

data Op = Positive | Zero deriving (Eq, Show)

instance (Ord f, Sized f, Ord v, Numbered v) => Symbolic (Prop1 f v) where
  type ConstantOf (Prop1 f v) = F1 f v
  type VariableOf (Prop1 f v) = v
  termsDL (Conj ps) = msum (map termsDL ps)
  termsDL (Disj ps) = msum (map termsDL ps)
  termsDL (SizeIs _ (Size c _)) = DList.fromList (map Var (Map.keys c))
  termsDL (Equal t u) = return t `mplus` return u
  termsDL (Less t u) = return t `mplus` return u
  substf = substProp

substProp :: (Ord f, Sized f, Ord v', Numbered v') => (v -> Tm f v') -> Prop1 f v -> Prop1 f v'
substProp sub (Conj ps) = Conj (map (substProp sub) ps)
substProp sub (Disj ps) = Disj (map (substProp sub) ps)
substProp sub (SizeIs op s) = SizeIs op (substSize sub s)
substProp sub (Equal t u) = Equal (foldTerm sub Fun t) (foldTerm sub Fun u)
substProp sub (Less t u) = less1' (foldTerm sub Fun t) (foldTerm sub Fun u)

flatten :: (Ord f, Sized f, Ord v, Numbered v) => Prop1 f v -> Prop
flatten = flatten1 . substProp (Var . number)

flatten1 :: (Ord f, Sized f) => Prop1 f Int -> Prop
flatten1 p = axioms :&& flattenIn n [] [p]
  where
    m = maximum (0:map succ (vars p))
    n = m + length cs
    cs = usort (funs p)
    cvs = Map.fromList (zip cs (map structVar [m..]))
    conVar x = Map.findWithDefault __ x cvs
    axioms =
      foldr (:&&) PTrue [ sizeVar x :>= K 1 | x <- usort (vars p) ] :&&
      foldr (:&&) PTrue [ conVar x :< conVar y | (x, y) <- zip cs (tail cs) ]
    flattenIn n ls [] = branch ls
    flattenIn n ls (p:ps) | p `elem` ls = flattenIn n ls ps
    flattenIn n ls (Conj ps:qs) = flattenIn n ls (ps++qs)
    flattenIn n ls (Disj ps:qs) =
      foldr (:||) PFalse [ flattenIn n ls (p:qs) | p <- ps ]
    flattenIn n ls (p@SizeIs{}:ps) = flattenIn n (p:ls) ps
    flattenIn n ls (Equal t u:ps) =
      case unify t u of
        Just sub ->
          flattenIn n [] (substf (evalSubst sub) (ls++ps))
        Nothing -> PFalse
    flattenIn n ls (p@(Less Var{} Var{}):ps) =
      flattenIn n (p:ls) ps
    flattenIn n ls (p@(Less (Var x) _):ps) =
      flattenIn (n+1+length ts) ls (p':p:ps)
      where
        (f:us) = map Var (take (1+length ts) [n..])
        p = Equal (Var x) (Fun App [f, us])
          Disj [
            HeadLess t u,
            argsLess us ts ]
    flattenIn n ls (Less t@(Fun f ts) u@(Var x):ps) =
      flattenIn (n+length ts) ls (p:ps)
      where
        us = map Var (take (length ts) [n..])
        p =
          Disj [
            HeadLess t u,
            argsLess ts us ]
    flattenIn n ls (p@HeadLess{}:ps) =
      flattenIn n (p:ls) ps

    branch ps = foldr (:&&) PTrue (map (literal (env ps)) ps)
    env ps = structVar . f
      where
        sub = Map.fromList (zip ts [n..])
        ts = filter isFun (usort (terms ps))
        f (Var x) = x
        f t = Map.findWithDefault __ t sub

    literal _ (SizeIs op s) = f op (encodeSize s)
      where
        f Positive = (:>  K 0)
        f Zero     = (:== K 0)
    literal env (Less t u) = env t :< env u
    literal env (HeadLess (Fun f _) (Fun g _))
      | f < g = PTrue
      | otherwise = PFalse
    literal env (HeadLess (Var x) (Var y)) = structVar x :< structVar y
    literal env (HeadLess (Var x) (Fun f _)) = structVar x :< conVar f
    literal env (HeadLess (Fun f _) (Var x)) = conVar f :< structVar x

sizeVar, structVar, headVar :: Numbered v => v -> Expr
sizeVar x = SAT.Var (toName (sizeNum x))
structVar x = SAT.Var (toName (number x*3+1))
headVar x = SAT.Var (toName (number x*3+2))
sizeNum :: Numbered v => v -> Int
sizeNum x = number x*3

less1, less1' :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> Prop1 f v
less1 t u =
  Disj [
    SizeIs Positive sz,
    Conj [SizeIs Zero sz, less1' t u]]
  where
    sz = termSize u `minus` (termSize t)

less1' (Fun f ts) (Fun g us) =
  case compare f g of
    LT -> Conj []
    GT -> Disj []
    EQ -> argsLess ts us
less1' t u | t == u = Disj []
less1' t u = Less t u

argsLess :: (Sized f, Ord f, Ord v, Numbered v) => [Tm f v] -> [Tm f v] -> Prop1 f v
argsLess [] [] = Disj []
argsLess (t:ts) (u:us) =
  Disj [
    less1 t u,
    Conj [Equal t u, argsLess ts us]]

-- Symbolic sizes of terms.
data Size a =
  Size {
    coeffs   :: Map a Integer,
    constant :: Integer }
  deriving (Eq, Show)

substSize :: (Sized f, Ord v') => (v -> Tm f v') -> Size v -> Size v'
substSize f (Size c x) =
  foldr plus (constSize x)
    [k `times` termSize (f v) | (v, k) <- Map.toList c]

evalSize :: (a -> Integer) -> Size a -> Integer
evalSize f (Size c x) = x + sum [ k * f v | (v, k) <- Map.toList c ]

encodeSize :: Numbered v => Size v -> Expr
encodeSize (Size c x) =
  foldr (:+) (K x)
    [k :* sizeVar v | (v, k) <- Map.toList c]

termSize :: (Sized f, Ord v) => Tm f v -> Size v
termSize = foldTerm var fun
  where
    fun f ss = foldr plus (constSize (fromIntegral (funSize f))) ss
    var x    = Size (Map.singleton x 1) 0

constSize :: Integer -> Size a
constSize n = Size Map.empty n

plus :: Ord a => Size a -> Size a -> Size a
plus (Size c x) (Size d y) = Size (Map.unionWith (+) c d) (x+y)

times :: Ord a => Integer -> Size a -> Size a
times n (Size c x) = Size (fmap (* n) c) (n*x)

minus :: Ord a => Size a -> Size a -> Size a
s `minus` s' = s `plus` times (-1) s'
