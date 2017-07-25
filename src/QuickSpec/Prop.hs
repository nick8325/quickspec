{-# LANGUAGE DeriveGeneric, TypeFamilies, DeriveFunctor, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module QuickSpec.Prop where

import Control.Monad
import qualified Data.DList as DList
import Data.Ord
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.Term
import GHC.Generics

data Prop a =
  (:=>:) {
    lhs :: [Equation a],
    rhs :: Equation a }
  deriving (Show, Generic, Functor)

instance Symbolic f a => Symbolic f (Prop a) where
  termsDL (lhs :=>: rhs) =
    termsDL lhs `mplus` termsDL rhs
  subst sub (lhs :=>: rhs) =
    subst sub lhs :=>: subst sub rhs

instance Ord a => Eq (Prop a) where
  x == y = x `compare` y == EQ
instance Ord a => Ord (Prop a) where
  compare = comparing (\p -> (usort (lhs p), rhs p))

infix 4 :=>:

literals :: Prop a -> [Equation a]
literals p = rhs p:lhs p

unitProp :: Equation a -> Prop a
unitProp p = [] :=>: p

instance Typed a => Typed (Prop a) where
  typ _ = typeOf True
  otherTypesDL p = DList.fromList (literals p) >>= typesDL
  typeSubst_ sub (lhs :=>: rhs) =
    map (typeSubst_ sub) lhs :=>: typeSubst_ sub rhs

instance Pretty a => Pretty (Prop a) where
  pPrint ([] :=>: rhs) = pPrint rhs
  pPrint p =
    hsep (punctuate (text " &") (map pPrint (lhs p))) <+> text "=>" <+> pPrint (rhs p)

data Equation a = a :=: a deriving (Show, Eq, Ord, Generic, Functor)

instance Symbolic f a => Symbolic f (Equation a) where
  termsDL (t :=: u) = termsDL t `mplus` termsDL u
  subst sub (t :=: u) = subst sub t :=: subst sub u

infix 5 :=:

instance Typed a => Typed (Equation a) where
  typ (t :=: _) = typ t
  otherTypesDL (t :=: u) = otherTypesDL t `mplus` typesDL u
  typeSubst_ sub (x :=: y) = typeSubst_ sub x :=: typeSubst_ sub y

instance Pretty a => Pretty (Equation a) where
  pPrintPrec _ _ (x :=: y) = pPrint x <+> text "=" <+> pPrint y

infix 4 ===
(===) :: a -> a -> Prop a
x === y = [] :=>: x :=: y
