{-# LANGUAGE DeriveFunctor, CPP #-}
module QuickSpec.Prop where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import Control.Applicative
import Data.Traversable
import Control.Monad.Trans.State.Strict
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Ord

type Prop = PropOf Term
data PropOf a =
  (:=>:) {
    lhs :: [Literal a],
    rhs :: Literal a } deriving (Show, Functor)

instance Ord a => Eq (PropOf a) where
  x == y = x `compare` y == EQ
instance Ord a => Ord (PropOf a) where
  compare = comparing (\p -> (usort (lhs p), rhs p))

infix 4 :=>:

propTerms :: PropOf a -> [a]
propTerms p = concatMap atomicTerms (lhs p) ++ atomicTerms (rhs p)

propLiterals :: PropOf a -> [Literal a]
propLiterals p = rhs p:lhs p

unitProp :: Literal a -> PropOf a
unitProp p = [] :=>: p

instance Typed a => Typed (PropOf a) where
  typ _ = boolType
  typeSubstA f (lhs :=>: rhs) =
    (:=>:) <$> traverse (typeSubstA f) lhs
           <*> typeSubstA f rhs

instance Pretty a => Pretty (PropOf a) where
  pretty ([] :=>: rhs) = pretty rhs
  pretty p =
    sep [
      fsep
        (punctuate (text "" <+> text "&")
          (map pretty (lhs p))) <+> text "=>",
      nest 2 (pretty (rhs p))]

data Literal a = a :=: a | Predicate :@: [a] deriving (Show, Functor, Eq, Ord)

infix 5 :@:
infix 5 :=:

atomicTerms :: Literal a -> [a]
atomicTerms (x :=: y) = [x, y]
atomicTerms (p :@: xs) = xs

instance Typed a => Typed (Literal a) where
  typ _ = boolType
  typeSubstA f (x :=: y) = (:=:) <$> typeSubstA f x <*> typeSubstA f y
  typeSubstA f (p :@: xs) = (:@:) <$> typeSubstA f p <*> traverse (typeSubstA f) xs

instance Pretty a => Pretty (Literal a) where
  pretty (x :=: y) = hang (pretty x <+> text "=") 2 (pretty y)
  pretty (p :@: xs) = pretty p <> parens (sep (punctuate comma (map pretty xs)))

data Predicate = Predicate {
  predName :: String,
  predType :: Type }
  deriving (Eq, Ord, Show)

instance Pretty Predicate where
  pretty = text . predName

instance Typed Predicate where
  typ = predType
  typeSubstA f (Predicate x ty) = Predicate x <$> typeSubstA f ty

boolType :: Type
boolType = typeOf (undefined :: Bool)
