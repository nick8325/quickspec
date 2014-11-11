{-# LANGUAGE TypeOperators, TypeFamilies, CPP #-}
module QuickSpec.Pruning.Constraints where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Utils
import QuickSpec.Pruning.Equation
import Data.Rewriting.Rule hiding (vars)
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

data Constraint f v = Tm f v :<: Tm f v deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Constraint f v) where
  pretty (t :<: u) = hang (pretty t <+> text "<") 2 (pretty u)

-- A rule only ever has one constraint,
-- in the worst case: rhs rule > lhs rule.
data ConstrainedRule f v =
    Always (Rule f v)
  | When (Constraint f v) (Rule f v)
  deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (ConstrainedRule f v) where
  pretty (Always rule) = pretty rule
  pretty (When cond rule) = hang (pretty rule <+> text "when") 2 (pretty cond)

-- A critical pair can have many constraints.
data ConstrainedPair f v =
  ConstrainedPair {
    constraints :: [Constraint f v],
    pair :: Equation f v }
  deriving Show

constrainRule :: (Sized f, Ord f, Ord v, Numbered v) => Rule f v -> Maybe (ConstrainedRule f v)
constrainRule rule@(Rule lhs rhs) =
  case orientTerms lhs rhs of
    Just GT -> Just (Always rule)
    Just _  -> Nothing
    Nothing -> Just (When (less rhs lhs) rule)

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

toProp1 :: (Ord f, Sized f, Ord v, Numbered v) => [Constraint f v] -> Prop1 f v
toProp1 cs = Conj [ less1 l r | l :<: r <- cs ]

minSize :: (Ord f, Sized f, Ord v, Numbered v) => [Constraint f v] -> Tm f v -> Maybe Integer
minSize cs t = do
  let p = toProp1 cs
      s = termSize t
  m <- checkSat (assert (flatten p) noProps)
  let sizeIn m = evalSize (\x -> fromMaybe __ (lookup (sizeNum x) m)) s
      loop n =
        case checkSat (assert (flatten (Conj [SizeIs Positive (constSize n `minus` s), p])) noProps) of
          Nothing -> Just n
          Just m  -> loop (sizeIn m)
  loop (sizeIn m)

minPairSize :: (Ord f, Sized f, Ord v, Numbered v) => ConstrainedPair f v -> Maybe Integer
minPairSize (ConstrainedPair cs (l :==: r)) =
  getMin $ Min (minSize cs l) `mappend` Min (minSize cs r)

subsumes :: (Ord f, Sized f, Ord v, Numbered v) => [Constraint f v] -> Constraint f v -> Bool
subsumes cs c = checkSat (assert p noProps) == Nothing
  where
    p = flatten (toProp1 cs) :&& Not (flatten (toProp1 [c]))

data Prop1 f v =
    Conj [Prop1 f v]
  | Disj [Prop1 f v]
  | SizeIs Op (Size v)
  | Equal (Tm f v) (Tm f v)
  | Less  (Tm f v) (Tm f v)
  deriving Show

data Op = Positive | Zero deriving Show

instance (Ord f, Sized f, Ord v, Numbered v) => Symbolic (Prop1 f v) where
  type ConstantOf (Prop1 f v) = f
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
substProp sub (Less t u) = less1 (foldTerm sub Fun t) (foldTerm sub Fun u)

flatten :: (Ord f, Sized f, Ord v, Numbered v) => Prop1 f v -> Prop
flatten = toProp . eliminateTerms . substProp (Var . number) . unDNF . eliminateEquals
  where
    toProp (Conj ps) = foldr (:&&) PTrue  (map toProp ps)
    toProp (Disj ps) = foldr (:||) PFalse (map toProp ps)
    toProp (SizeIs op s) = f op (encodeSize s)
      where
        f Positive = (:>  K 0)
        f Zero     = (:== K 0)
    toProp (Less (Var x) (Var y)) = structVar x :< structVar y
    unDNF = Disj . map Conj

eliminateTerms :: (Ord f, Sized f) => Prop1 f Int -> Prop1 f Int
eliminateTerms p = elim p
  where
    ts  = filter isFun (usort (terms p))
    vs  = usort (vars p)
    n   = maximum (0:map succ vs)
    sub = Map.fromList (zip ts [n..])
    elim (Conj ps)  = Conj (map elim ps)
    elim (Disj ps)  = Disj (map elim ps)
    elim p@SizeIs{} = p
    elim (Less t u) = Less (elimTerm t) (elimTerm u)
    elimTerm t@Fun{} = Var (Map.findWithDefault __ t sub)
    elimTerm t@Var{} = t

eliminateEquals :: (Ord f, Sized f, Ord v, Numbered v) => Prop1 f v -> [[Prop1 f v]]
eliminateEquals p = concatMap branch (dnf p)
  where
    dnf (Disj ps) = concatMap dnf ps
    dnf (Conj ps) = map concat (sequence (map dnf ps))
    dnf t         = [[t]]
    branch ps =
      case sortBy (comparing (not . isEqual)) ps of
        (Equal t u:ps) | t == u ->
          branch ps
        (Equal t u:ps) ->
          case unify t u of
            Just sub ->
              eliminateEquals (Conj (map (substf (evalSubst sub)) ps))
            Nothing ->
              []
        _ -> [ps]
    isEqual Equal{} = True
    isEqual _       = False

sizeVar, structVar :: Numbered v => v -> Expr
sizeVar x = SAT.Var (toName (sizeNum x))
structVar x = SAT.Var (toName (number x*2+1))
sizeNum :: Numbered v => v -> Int
sizeNum x = number x*2

less1, less1' :: (Sized f, Ord f, Ord v, Numbered v) => Tm f v -> Tm f v -> Prop1 f v
less1 t u =
  Disj [
    SizeIs Positive sz,
    Conj [SizeIs Zero sz, less1' t u]]
  where
    sz = termSize t `minus` (termSize u)

less1' (Fun f ts) (Fun g us) =
  case compare f g of
    LT -> Conj []
    GT -> Disj []
    EQ -> argsLess ts us
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
  deriving Show

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
