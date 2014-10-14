{-# LANGUAGE DeriveFunctor #-}
module QuickSpec.Prop where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import Control.Applicative
import Data.Traversable

type Prop = PropOf Term
data PropOf a =
  (:=>:) {
    lhs :: [Literal a],
    rhs :: Literal a } deriving (Show, Functor)

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
  pretty p = pretty (lhs p) <+> text "=>" <+> pretty (rhs p)

data Literal a = a :=: a | Predicate :@: [a] deriving (Show, Functor)

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
  pretty (x :=: y) = pretty x <+> text "=" <+> pretty y
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
