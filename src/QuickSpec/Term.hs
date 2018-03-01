-- | This module is internal to QuickSpec.
--
-- Typed terms and operations on them.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds, DeriveGeneric, DeriveAnyClass, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, TypeOperators, DeriveFunctor, FlexibleContexts #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Base, module Twee.Pretty) where

import QuickSpec.Type
import QuickSpec.Utils
import Control.Monad
import GHC.Generics(Generic)
import Test.QuickCheck(CoArbitrary)
import Data.DList(DList)
import qualified Data.DList as DList
import Twee.Base(Arity(..), Pretty(..), PrettyTerm(..), TermStyle(..), EqualsBonus, prettyPrint)
import Twee.Pretty
import qualified Data.Map.Strict as Map
import Data.List

-- | A typed term.
data Term f = Var {-# UNPACK #-} !Var | App !f ![Term f]
  deriving (Eq, Ord, Show, Functor)

-- | A variable, which has a type and a number.
data Var = V { var_ty :: !Type, var_id :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show, Generic, CoArbitrary)

instance Typed Var where
  typ x = var_ty x
  otherTypesDL _ = mzero
  typeSubst_ sub (V ty x) = V (typeSubst_ sub ty) x

-- | A class for things that contain terms.
class Symbolic f a | a -> f where
  -- | A different list of all terms contained in the thing.
  termsDL :: a -> DList (Term f)
  -- | Apply a substitution to all terms in the thing.
  subst :: (Var -> Term f) -> a -> a

instance Symbolic f (Term f) where
  termsDL = return
  subst sub (Var x) = sub x
  subst sub (App f ts) = App f (map (subst sub) ts)

instance Symbolic f a => Symbolic f [a] where
  termsDL = msum . map termsDL
  subst sub = map (subst sub)

class Sized a where
  size :: a -> Int

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

-- | Is a term an application (i.e. not a variable)?
isApp :: Term f -> Bool
isApp App{} = True
isApp Var{} = False

-- | Is a term a variable?
isVar :: Term f -> Bool
isVar = not . isApp

-- | All terms contained in a `Symbolic`.
terms :: Symbolic f a => a -> [Term f]
terms = DList.toList . termsDL

-- | All function symbols appearing in a `Symbolic`, in order of appearance,
-- with duplicates included.
funs :: Symbolic f a => a -> [f]
funs x = [ f | t <- terms x, App f _ <- subterms t ]

-- | All variables appearing in a `Symbolic`, in order of appearance,
-- with duplicates included.
vars :: Symbolic f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subterms t ]

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
mapVar f (App g xs) = App g (map (mapVar f) xs)

-- | Find all subterms of a term. Includes the term itself.
subterms :: Term f -> [Term f]
subterms t = t:properSubterms t

-- | Find all subterms of a term. Does not include the term itself.
properSubterms :: Term f -> [Term f]
properSubterms (App _ ts) = concatMap subterms ts
properSubterms _ = []

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
    eval (App f ts) = do
      f <- fun f
      ts <- mapM eval ts
      return (foldl apply f ts)

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

-- | A standard term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure f = (Int, Int, MeasureFuns f, Int, [Var])
-- | Compute the term ordering for a term.
measure :: Sized f => Term f -> Measure f
measure t =
  (size t, -length (vars t), MeasureFuns (skel t),
   -length (usort (vars t)), vars t)
  where
    skel (Var (V ty _)) = Var (V ty 0)
    skel (App f ts) = App f (map skel ts)

-- | A helper for `Measure`.
newtype MeasureFuns f = MeasureFuns (Term f)
instance Ord f => Eq (MeasureFuns f) where
  t == u = compare t u == EQ
instance Ord f => Ord (MeasureFuns f) where
  compare (MeasureFuns t) (MeasureFuns u) = compareFuns t u

-- | A helper for `Measure`.
compareFuns :: Ord f => Term f -> Term f -> Ordering
compareFuns (Var x) (Var y) = compare x y
compareFuns Var{} App{} = LT
compareFuns App{} Var{} = GT
compareFuns (App f ts) (App g us) =
  compare f g `orElse`
  compare (map MeasureFuns ts) (map MeasureFuns us)

----------------------------------------------------------------------
-- * Data types a la carte-ish.
----------------------------------------------------------------------

-- | A sum type. Intended to be used to build the type of function
-- symbols. Comes with instances that are useful for QuickSpec.
data a :+: b = Inl a | Inr b deriving (Eq, Ord)

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
