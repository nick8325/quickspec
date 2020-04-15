-- | This module is internal to QuickSpec.
--
-- Typed terms and operations on them.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds, DeriveGeneric, DeriveAnyClass, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, TypeOperators, DeriveFunctor, FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module QuickSpec.Internal.Term(module QuickSpec.Internal.Term, module Twee.Base, module Twee.Pretty) where

import QuickSpec.Internal.Type
import QuickSpec.Internal.Utils
import Control.Monad
import GHC.Generics(Generic)
import Test.QuickCheck(CoArbitrary(..))
import Data.DList(DList)
import qualified Data.DList as DList
import Twee.Base(Pretty(..), PrettyTerm(..), TermStyle(..), EqualsBonus, prettyPrint)
import Twee.Pretty
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.List
import Data.Ord

-- | A typed term.
data Term f = Var {-# UNPACK #-} !Var | Fun !f | !(Term f) :$: !(Term f)
  deriving (Eq, Ord, Show, Functor)

-- | A variable, which has a type and a number.
data Var = V { var_ty :: !Type, var_id :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show, Generic)

instance CoArbitrary Var where
  coarbitrary = coarbitrary . var_id

instance Typed Var where
  typ x = var_ty x
  otherTypesDL _ = mzero
  typeSubst_ sub (V ty x) = V (typeSubst_ sub ty) x

match :: Eq f => Term f -> Term f -> Maybe (Map Var (Term f))
match (Var x) t = Just (Map.singleton x t)
match (Fun f) (Fun g)
  | f == g = Just Map.empty
  | otherwise = Nothing
match (f :$: x) (g :$: y) = do
  m1 <- match f g
  m2 <- match x y
  guard (and [t == u | (t, u) <- Map.elems (Map.intersectionWith (,) m1 m2)])
  return (Map.union m1 m2)

unify :: Eq f => Term f -> Term f -> Maybe (Map Var (Term f))
unify t u = loop Map.empty [(t, u)]
  where
    loop sub [] = Just sub
    loop sub ((Fun f, Fun g):xs)
      | f == g = loop sub xs
    loop sub ((f :$: x, g :$: y):xs) =
      loop sub ((f, g):(x, y):xs)
    loop sub ((Var x, t):xs)
      | t == Var x = loop sub xs
      | x `elem` vars t = Nothing
      | otherwise =
        loop
          (Map.insert x t (fmap (replace x t) sub))
          [(replace x t u, replace x t v) | (u, v) <- xs]
    loop sub ((t, Var x):xs) = loop sub ((Var x, t):xs)

    replace x t (Var y) | x == y = t
    replace _ _ t = t

-- | A class for things that contain terms.
class Symbolic f a | a -> f where
  -- | A different list of all terms contained in the thing.
  termsDL :: a -> DList (Term f)
  -- | Apply a substitution to all terms in the thing.
  subst :: (Var -> Term f) -> a -> a

instance Symbolic f (Term f) where
  termsDL = return
  subst sub (Var x) = sub x
  subst _ (Fun x) = Fun x
  subst sub (t :$: u) = subst sub t :$: subst sub u

instance Symbolic f a => Symbolic f [a] where
  termsDL = msum . map termsDL
  subst sub = map (subst sub)

class Sized a where
  size :: a -> Int

instance Sized f => Sized (Term f) where
  size (Var _) = 1
  size (Fun f) = size f
  size (t :$: u) =
    size t + size u +
    -- Penalise applied function variables, because they can be used
    -- to build many many terms without any constants at all
    case t of
      Var _ -> 1
      _ -> 0

instance Pretty Var where
  pPrint x = parens $ text "X" <#> pPrint (var_id x+1) <+> text "::" <+> pPrint (var_ty x)
  --pPrint x = text "X" <#> pPrint (var_id x+1)

instance PrettyTerm f => Pretty (Term f) where
  pPrintPrec l p (Var x :@: ts) =
    pPrintTerm curried l p (pPrint x) ts
  pPrintPrec l p (Fun f :@: ts) =
    pPrintTerm (termStyle f) l p (pPrint f) ts

-- | All terms contained in a `Symbolic`.
terms :: Symbolic f a => a -> [Term f]
terms = DList.toList . termsDL

-- | All function symbols appearing in a `Symbolic`, in order of appearance,
-- with duplicates included.
funs :: Symbolic f a => a -> [f]
funs x = [ f | t <- terms x, Fun f <- subterms t ]

-- | All variables appearing in a `Symbolic`, in order of appearance,
-- with duplicates included.
vars :: Symbolic f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subterms t ]

-- | Decompose a term into a head and a list of arguments.
pattern f :@: ts <- (getApp -> (f, ts)) where
  f :@: ts = foldl (:$:) f ts

getApp :: Term f -> (Term f, [Term f])
getApp (t :$: u) = (f, ts ++ [u])
  where
    (f, ts) = getApp t
getApp t = (t, [])

-- | Compute the number of a variable which does /not/ appear in the `Symbolic`.
freeVar :: Symbolic f a => a -> Int
freeVar x = maximum (0:map (succ . var_id) (vars x))

-- | Count how many times a given function symbol occurs.
occ :: (Eq f, Symbolic f a) => f -> a -> Int
occ x t = length (filter (== x) (funs t))

-- | Count how many times a given variable occurs.
occVar :: Symbolic f a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

-- | Map a function over variables.
mapVar :: (Var -> Var) -> Term f -> Term f
mapVar f (Var x) = Var (f x)
mapVar _ (Fun x) = Fun x
mapVar f (t :$: u) = mapVar f t :$: mapVar f u

-- | Find all subterms of a term. Includes the term itself.
subterms :: Term f -> [Term f]
subterms t = t:properSubterms t

-- | Find all subterms of a term. Does not include the term itself.
properSubterms :: Term f -> [Term f]
properSubterms (t :$: u) = subterms t ++ subterms u
properSubterms _ = []

subtermsFO :: Term f -> [Term f]
subtermsFO t = t:properSubtermsFO t

properSubtermsFO :: Term f -> [Term f]
properSubtermsFO (_f :@: ts) = concatMap subtermsFO ts
properSubtermsFO _ = []

-- | Renames variables so that they appear in a canonical order.
-- Also makes sure that variables of different types have different numbers.
canonicalise :: Symbolic fun a => a -> a
canonicalise t = subst (\x -> Map.findWithDefault undefined x sub) t
  where
    sub =
      Map.fromList
        [(x, Var (V ty n))
        | (x@(V ty _), n) <- zip (nub (vars t)) [0..]]

-- | Evaluate a term, given a valuation for variables and function symbols.
evalTerm :: (Typed fun, Apply a, Monad m) => (Var -> m a) -> (fun -> m a) -> Term fun -> m a
evalTerm var fun = eval
  where
    eval (Var x) = var x
    eval (Fun f) = fun f
    eval (t :$: u) = liftM2 apply (eval t) (eval u)

instance Typed f => Typed (Term f) where
  typ (Var x) = typ x
  typ (Fun f) = typ f
  typ (t :$: _) = typeDrop 1 (typ t)

  otherTypesDL (Var _) = mempty
  otherTypesDL (Fun f) = typesDL f
  otherTypesDL (t :$: u) = typesDL t `mplus` typesDL u

  typeSubst_ sub = tsub
    where
      tsub (Var x) = Var (typeSubst_ sub x)
      tsub (Fun f) = Fun (typeSubst_ sub f)
      tsub (t :$: u) =
        typeSubst_ sub t :$: typeSubst_ sub u

instance (PrettyTerm f, Typed f) => Apply (Term f) where
  tryApply t u = do
    tryApply (typ t) (typ u)
    return (t :$: u)

depth :: Term f -> Int
depth Var{} = 1
depth Fun{} = 1
depth (t :$: u) = depth t `max` (1+depth u)

-- | A standard term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure f = (Int, Int, Int, Int, MeasureFuns f, Int, [Var])
-- | Compute the term ordering for a term.
measure :: (Sized f, Typed f) => Term f -> Measure f
measure t =
  (depth t, size t, missing t, -length (vars t), MeasureFuns (skel t),
   -length (usort (vars t)), vars t)
  where
    skel (Var (V ty _)) = Var (V ty 0)
    skel (Fun f) = Fun f
    skel (t :$: u) = skel t :$: skel u
    -- Prefer fully-applied terms to partially-applied ones.
    -- This function counts how many unsaturated function applications
    -- occur in a term.
    missing (Fun f :@: ts) =
      typeArity (typ f) - length ts + sum (map missing ts)
    missing (Var _ :@: ts) =
      sum (map missing ts)

-- | A helper for `Measure`.
newtype MeasureFuns f = MeasureFuns (Term f)
instance Ord f => Eq (MeasureFuns f) where
  t == u = compare t u == EQ
instance Ord f => Ord (MeasureFuns f) where
  compare (MeasureFuns t) (MeasureFuns u) = compareFuns t u

-- | A helper for `Measure`.
compareFuns :: Ord f => Term f -> Term f -> Ordering
compareFuns (f :@: ts) (g :@: us) =
  compareHead f g `mappend` comparing (map MeasureFuns) ts us
  where
    compareHead (Var x) (Var y) = compare x y
    compareHead (Var _) _ = LT
    compareHead _ (Var _) = GT
    compareHead (Fun f) (Fun g) = compare f g
    compareHead _ _ = error "viewApp"

----------------------------------------------------------------------
-- * Data types a la carte-ish.
----------------------------------------------------------------------

-- | A sum type. Intended to be used to build the type of function
-- symbols. Comes with instances that are useful for QuickSpec.
data a :+: b = Inl a | Inr b deriving (Eq, Ord)

instance (Sized fun1, Sized fun2) => Sized (fun1 :+: fun2) where
  size (Inl x) = size x
  size (Inr x) = size x

instance (Typed fun1, Typed fun2) => Typed (fun1 :+: fun2) where
  typ (Inl x) = typ x
  typ (Inr x) = typ x
  otherTypesDL (Inl x) = otherTypesDL x
  otherTypesDL (Inr x) = otherTypesDL x
  typeSubst_ sub (Inl x) = Inl (typeSubst_ sub x)
  typeSubst_ sub (Inr x) = Inr (typeSubst_ sub x)

instance (Pretty fun1, Pretty fun2) => Pretty (fun1 :+: fun2) where
  pPrintPrec l p (Inl x) = pPrintPrec l p x
  pPrintPrec l p (Inr x) = pPrintPrec l p x

instance (PrettyTerm fun1, PrettyTerm fun2) => PrettyTerm (fun1 :+: fun2) where
  termStyle (Inl x) = termStyle x
  termStyle (Inr x) = termStyle x
