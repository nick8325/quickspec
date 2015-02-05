{-# LANGUAGE DeriveFunctor, CPP, TypeFamilies #-}
module QuickSpec.Prop where

#include "errors.h"
import Control.Monad
import qualified Data.DList as DList
import Data.Ord
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import qualified Data.Map as Map
import Data.Rewriting.Substitution.Type

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

literals :: PropOf a -> [Literal a]
literals p = rhs p:lhs p

unitProp :: Literal a -> PropOf a
unitProp p = [] :=>: p

instance (Symbolic a, Typed a) => Typed (PropOf a) where
  typ _ = boolType
  otherTypesDL p = DList.fromList (literals p) >>= typesDL
  typeSubst sub (lhs :=>: rhs) =
    map (typeSubst sub) lhs :=>: typeSubst sub rhs
instance Symbolic a => Symbolic (PropOf a) where
  type ConstantOf (PropOf a) = ConstantOf a
  type VariableOf (PropOf a) = VariableOf a
  termsDL p = DList.fromList (literals p) >>= termsDL
  substf sub (lhs :=>: rhs) = map (substf sub) lhs :=>: substf sub rhs

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

instance Symbolic a => Symbolic (Literal a) where
  type ConstantOf (Literal a) = ConstantOf a
  type VariableOf (Literal a) = VariableOf a
  termsDL l = literalTermsDL l >>= termsDL
  substf sub (t :=: u) = substf sub t :=: substf sub u
  substf sub (p :@: ts) = p :@: map (substf sub) ts

instance (Symbolic a, Typed a) => Typed (Literal a) where
  typ _ = boolType
  otherTypesDL l = literalTermsDL l >>= typesDL
  typeSubst sub (x :=: y) = typeSubst sub x :=: typeSubst sub y
  typeSubst sub (p :@: ts) = typeSubst sub p :@: map (typeSubst sub) ts

propTerms :: PropOf a -> [a]
propTerms p = literals p >>= DList.toList . literalTermsDL

literalTermsDL :: Literal a -> DList.DList a
literalTermsDL (t :=: u) = return u `mplus` return t
literalTermsDL (p :@: ts) = DList.fromList ts

propType :: Typed a => PropOf a -> Type
propType (_ :=>: p :@: ts) = typ p
propType (_ :=>: t :=: u) = typ t

instance Pretty a => Pretty (Literal a) where
  pretty (x :=: y) = hang (pretty x <+> text "=") 2 (pretty y)
  pretty (p :@: xs) = pretty p <> parens (sep (punctuate comma (map pretty xs)))

data Predicate = Predicate {
  predName :: String,
  predType :: Type,
  predGeneralType :: Poly Type }
  deriving (Eq, Ord, Show)

instance Pretty Predicate where
  pretty = text . predName

instance Typed Predicate where
  typ = predType
  typeSubst sub (Predicate x ty pty) = Predicate x (typeSubst sub ty) pty

boolType :: Type
boolType = typeOf (undefined :: Bool)

regeneralise :: Prop -> Prop
regeneralise = restrict . unPoly . generalise . canonicalise
  where
    generalise (lhs :=>: rhs) =
      polyApply (:=>:) (polyList (map genLit lhs)) (genLit rhs)
    genLit (p :@: ts) =
      polyApply (:@:) (genPred p) (polyList (map genTerm ts))
    genLit (t :=: u) = polyApply (:=:) (genTerm t) (genTerm u)
    genTerm (Fun f []) = polyMap (\f -> Fun f []) (genCon f)
    genTerm (Fun f ts) = apply (genTerm (Fun f (init ts))) (genTerm (last ts))
    genTerm (Var x) = polyMap Var (genVar x)

    genPred p = poly (p { predType = unPoly (predGeneralType p) })
    genCon  f = poly (f { conValue = unPoly (conGeneralValue f), conArity = 0 })
    genVar (Variable n _) = poly (Variable n (typeOf (undefined :: A)))

    restrict prop = typeSubst f prop
      where
        f ty = Map.findWithDefault (Var ty) ty (toMap sub)
        Just sub = unifyMany Arrow cs
        cs = [(typ x, typ y) | x:xs <- vs, y <- xs] ++ concatMap litCs (lhs prop) ++ litCs (rhs prop)
        vs = partitionBy varNumber (vars prop)
    litCs (t :=: u) = [(typ t, typ u)] ++ termCs t ++ termCs u
    litCs (p :@: ts) = [(typ p, arrowType (map typ ts) (typeOf True))] ++ concatMap termCs ts
    termCs Var{} = []
    termCs t@(Fun f ts) = [(typ f, arrowType (map typ ts) (typ t))] ++ concatMap termCs ts
