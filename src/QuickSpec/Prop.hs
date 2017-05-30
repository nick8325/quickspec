{-# LANGUAGE DeriveGeneric, TypeFamilies, DeriveFunctor #-}
module QuickSpec.Prop where

import Control.Monad
import qualified Data.DList as DList
import Data.Ord
import QuickSpec.Type
import QuickSpec.Utils
import Twee.Pretty
import Twee.Base
import GHC.Generics

data Prop a =
  (:=>:) {
    lhs :: [Equation a],
    rhs :: Equation a }
  deriving (Show, Generic, Functor)

instance Symbolic a => Symbolic (Prop a) where
  type ConstantOf (Prop a) = ConstantOf a

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
    sep [
      fsep
        (punctuate (text "" <+> text "&")
          (map pPrint (lhs p))) <+> text "=>",
      nest 2 (pPrint (rhs p))]

data Equation a = a :=: a deriving (Show, Eq, Ord, Generic, Functor)

instance Symbolic a => Symbolic (Equation a) where
  type ConstantOf (Equation a) = ConstantOf a

infix 5 :=:

instance Typed a => Typed (Equation a) where
  typ (t :=: _) = typ t
  otherTypesDL (t :=: u) = otherTypesDL t `mplus` typesDL u
  typeSubst_ sub (x :=: y) = typeSubst_ sub x :=: typeSubst_ sub y

instance Pretty a => Pretty (Equation a) where
  pPrintPrec _ _ (x :=: y) = hang (pPrint x <+> text "=") 2 (pPrint y)

infix 4 ===
(===) :: a -> a -> Prop a
x === y = [] :=>: x :=: y
