-- Typed terms.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds, DeriveGeneric, DeriveAnyClass, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, TypeOperators, DeriveFunctor, FlexibleContexts #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Base, module Twee.Pretty) where

import QuickSpec.Type
import QuickSpec.Utils
import Control.Monad
import GHC.Generics(Generic)
import Test.QuickCheck(CoArbitrary)
import Data.DList(DList)
import qualified Data.DList as DList
import Twee.Base(Sized(..), Arity(..), Pretty(..), PrettyTerm(..), TermStyle(..), EqualsBonus, prettyPrint)
import Twee.Pretty
import qualified Data.Map.Strict as Map
import Data.List
import Data.Reflection

data Term f = Var {-# UNPACK #-} !Var | App !f ![Term f]
  deriving (Eq, Ord, Show, Functor)

data Var = V { var_ty :: !Type, var_id :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show, Generic, CoArbitrary)

instance Typed Var where
  typ x = var_ty x
  otherTypesDL _ = mzero
  typeSubst_ sub (V ty x) = V (typeSubst_ sub ty) x

class Symbolic f a | a -> f where
  termsDL :: a -> DList (Term f)
  subst :: (Var -> Term f) -> a -> a

instance Symbolic f (Term f) where
  termsDL = return
  subst sub (Var x) = sub x
  subst sub (App f ts) = App f (map (subst sub) ts)

instance Symbolic f a => Symbolic f [a] where
  termsDL = msum . map termsDL
  subst sub = map (subst sub)

instance Sized f => Sized (Term f) where
  size (Var _) = 1
  size (App f ts) = size f + sum (map size ts)

instance Pretty Var where
  --pPrint x = parens $ text "X" <> pPrint (var_id x+1) <+> text "::" <+> pPrint (var_ty x)
  pPrint x = text "X" <> pPrint (var_id x+1)

instance PrettyTerm f => Pretty (Term f) where
  pPrintPrec l p (Var x) = pPrintPrec l p x
  pPrintPrec l p (App f xs) =
    pPrintTerm (termStyle f) l p (pPrint f) xs

isApp :: Term f -> Bool
isApp App{} = True
isApp Var{} = False

isVar :: Term f -> Bool
isVar = not . isApp

terms :: Symbolic f a => a -> [Term f]
terms = DList.toList . termsDL

funs :: Symbolic f a => a -> [f]
funs x = [ f | t <- terms x, App f _ <- subterms t ]

vars :: Symbolic f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subterms t ]

freeVar :: Symbolic f a => a -> Int
freeVar x = maximum (0:map (succ . var_id) (vars x))

occ :: (Eq f, Symbolic f a) => f -> a -> Int
occ x t = length (filter (== x) (funs t))

occVar :: Symbolic f a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

mapVar :: (Var -> Var) -> Term f -> Term f
mapVar f (Var x) = Var (f x)
mapVar f (App g xs) = App g (map (mapVar f) xs)

subterms, properSubterms :: Term f -> [Term f]
subterms t = t:properSubterms t
properSubterms (App _ ts) = concatMap subterms ts
properSubterms _ = []

-- Introduces variables in a canonical order.
-- Also makes sure that variables of different types have different numbers
canonicalise :: Symbolic fun a => a -> a
canonicalise t = subst (\x -> Map.findWithDefault undefined x sub) t
  where
    sub =
      Map.fromList
        [(x, Var (V ty n))
        | (x@(V ty _), n) <- zip (nub (vars t)) [0..]]

class Eval term val where
  eval :: (Var -> val) -> term -> val

instance (Typed fun, Given Type, Apply a, Eval fun a) => Eval (Term fun) a where
  eval env = evaluateTerm (eval env) env

evaluateTerm :: (Typed fun, Given Type, Apply a) => (fun -> a) -> (Var -> a) -> Term fun -> a
evaluateTerm fun var = eval
  where
    eval (Var x) = var x
    eval (App f ts) =
      foldl apply (fun (defaultTo given f)) (map eval ts)

instance Typed f => Typed (Term f) where
  typ (Var x) = typ x
  typ (App f ts) =
    typeDrop (length ts) (typ f)

  otherTypesDL (Var _) = mempty
  otherTypesDL (App f ts) =
    typesDL f `mplus` typesDL ts

  typeSubst_ sub = tsub
    where
      tsub (Var x) = Var (typeSubst_ sub x)
      tsub (App f ts) =
        App (typeSubst_ sub f) (map tsub ts)

-- A standard term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure f = (Int, Int, MeasureFuns f, Int, [Var])
measure :: Sized f => Term f -> Measure f
measure t =
  (size t, -length (vars t), MeasureFuns (skel t),
   -length (usort (vars t)), vars t)
  where
    skel (Var (V ty _)) = Var (V ty 0)
    skel (App f ts) = App f (map skel ts)

newtype MeasureFuns f = MeasureFuns (Term f)
instance Ord f => Eq (MeasureFuns f) where
  t == u = compare t u == EQ
instance Ord f => Ord (MeasureFuns f) where
  compare (MeasureFuns t) (MeasureFuns u) = compareFuns t u

compareFuns :: Ord f => Term f -> Term f -> Ordering
compareFuns (Var x) (Var y) = compare x y
compareFuns Var{} App{} = LT
compareFuns App{} Var{} = GT
compareFuns (App f ts) (App g us) =
  compare f g `orElse`
  compare (map MeasureFuns ts) (map MeasureFuns us)

----------------------------------------------------------------------
-- Data types a la carte-ish.
----------------------------------------------------------------------

data a :+: b = Inl a | Inr b deriving (Eq, Ord)

instance (Eval fun1 a, Eval fun2 a) => Eval (fun1 :+: fun2) a where
  eval env (Inl x) = eval env x
  eval env (Inr x) = eval env x

instance (Sized fun1, Sized fun2) => Sized (fun1 :+: fun2) where
  size (Inl x) = size x
  size (Inr x) = size x

instance (Arity fun1, Arity fun2) => Arity (fun1 :+: fun2) where
  arity (Inl x) = arity x
  arity (Inr x) = arity x

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
