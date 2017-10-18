-- Typed terms.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds, DeriveGeneric, DeriveAnyClass, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Base, module Twee.Pretty) where

import QuickSpec.Type
import QuickSpec.Utils
import Control.Monad
import GHC.Generics
import Test.QuickCheck(CoArbitrary)
import Data.DList(DList)
import qualified Data.DList as DList
import Twee.Base(Sized(..), Arity(..), Pretty(..), PrettyTerm(..), TermStyle(..), EqualsBonus, prettyPrint)
import Twee.Pretty

data Term f = Var {-# UNPACK #-} !Var | App !f ![Term f]
  deriving (Eq, Ord, Show)

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
  pPrint x = text "X" <> pPrint (var_id x+1)

instance PrettyTerm f => Pretty (Term f) where
  pPrintPrec l p (Var x) = pPrintPrec l p x
  pPrintPrec l p (App f xs) =
    pPrintTerm (termStyle f) l p (pPrint f) xs

terms :: Symbolic f a => a -> [Term f]
terms = DList.toList . termsDL

funs :: Symbolic f a => a -> [f]
funs x = [ f | t <- terms x, App f _ <- subterms t ]

vars :: Symbolic f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subterms t ]

occ :: (Eq f, Symbolic f a) => f -> a -> Int
occ x t = length (filter (== x) (funs t))

occVar :: Symbolic f a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

subterms, properSubterms :: Term f -> [Term f]
subterms t = t:properSubterms t
properSubterms (App _ ts) = concatMap subterms ts
properSubterms _ = []

class Eval term val where
  eval :: (Var -> val) -> term -> val

instance (Apply a, Eval fun a) => Eval (Term fun) a where
  eval env = evaluateTerm (eval env) env

evaluateTerm :: Apply a => (fun -> a) -> (Var -> a) -> Term fun -> a
evaluateTerm fun var = eval
  where
    eval (Var x) = var x
    eval (App f ts) =
      foldl apply (fun f) (map eval ts)

instance Typed f => Typed (Term f) where
  typ (Var x) = typ x
  typ (App f ts) =
    typeDrop (length ts) (typ f)

  otherTypesDL (Var _) = mempty
  otherTypesDL (App f ts) =
    otherTypesDL f `mplus` otherTypesDL ts

  typeSubst_ sub = tsub
    where
      tsub (Var x) = Var (typeSubst_ sub x)
      tsub (App f ts) =
        App (typeSubst_ sub f) (map tsub ts)

-- A standard term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure f = (Int, Int, MeasureFuns f, Int, [Var])
measure :: (Sized f, Ord f) => Term f -> Measure f
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
