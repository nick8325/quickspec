{-# LANGUAGE DeriveFunctor, CPP, TypeFamilies, FlexibleContexts #-}
module QuickSpec.Prop where

#include "errors.h"
import Control.Monad
import qualified Data.DList as DList
import Data.Ord
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import qualified Data.Map as Map
import Twee.Base

type Prop = PropOf (Term Constant)
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
  typeReplace sub (lhs :=>: rhs) =
    map (typeReplace sub) lhs :=>: typeReplace sub rhs
instance Symbolic a => Symbolic (PropOf a) where
  type ConstantOf (PropOf a) = ConstantOf a
  term = __
  termsDL p = DList.fromList (literals p) >>= termsDL
  replace sub (lhs :=>: rhs) = map (replace sub) lhs :=>: replace sub rhs

instance Pretty a => Pretty (PropOf a) where
  pPrint ([] :=>: rhs) = pPrint rhs
  pPrint p =
    sep [
      fsep
        (punctuate (text "" <+> text "&")
          (map pPrint (lhs p))) <+> text "=>",
      nest 2 (pPrint (rhs p))]

data Literal a = a :=: a | Predicate :@: [a] deriving (Show, Functor, Eq, Ord)

infix 5 :@:
infix 5 :=:

instance Symbolic a => Symbolic (Literal a) where
  type ConstantOf (Literal a) = ConstantOf a
  term = __
  termsDL l = literalTermsDL l >>= termsDL
  replace sub (t :=: u) = replace sub t :=: replace sub u
  replace sub (p :@: ts) = p :@: map (replace sub) ts

instance (Symbolic a, Typed a) => Typed (Literal a) where
  typ _ = boolType
  otherTypesDL l = literalTermsDL l >>= typesDL
  typeReplace sub (x :=: y) = typeReplace sub x :=: typeReplace sub y
  typeReplace sub (p :@: ts) = typeReplace sub p :@: map (typeReplace sub) ts

propTerms :: PropOf a -> [a]
propTerms p = literals p >>= DList.toList . literalTermsDL

literalTermsDL :: Literal a -> DList.DList a
literalTermsDL (t :=: u) = return u `mplus` return t
literalTermsDL (p :@: ts) = DList.fromList ts

propType :: Typed a => PropOf a -> Type
propType (_ :=>: p :@: ts) = typ p
propType (_ :=>: t :=: u) = typ t

instance Pretty a => Pretty (Literal a) where
  pPrint (x :=: y) = hang (pPrint x <+> text "=") 2 (pPrint y)
  pPrint (p :@: xs) = pPrint p <> parens (sep (punctuate comma (map pPrint xs)))

data Predicate = Predicate {
  predName :: String,
  predType :: Type,
  predGeneralType :: Poly Type }
  deriving (Eq, Ord, Show)

instance Pretty Predicate where
  pPrint = text . predName

instance Typed Predicate where
  typ = predType
  typeReplace sub (Predicate x ty pty) = Predicate x (typeReplace sub ty) pty

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
    -- FIXME if we discover a unit law x = y :: (), won't it be falsely
    -- generalised to x = y :: a? Instead of using A here, need to freshen
    -- all type variables in type of var.
    -- Currently this isn't a problem since we can't get a law with a
    -- variable on both sides, but may break with smarter schema instantiation
    genTerm x@Var{} =
      poly (app (Id (typeOf (undefined :: A))) [x])
    genTerm (App (Id _) [x@Var{}]) =
      poly (app (Id (typeOf (undefined :: A))) [x])
    genTerm (App f []) = polyMap (\f -> app f []) (genCon f)
    genTerm (App f ts) = apply (genTerm (app f (init ts))) (genTerm (last ts))

    genPred p = poly (p { predType = unPoly (predGeneralType p) })
    genCon  f = poly (f { conValue = unPoly (conGeneralValue f), conArity = 0 })

    restrict prop = typeSubst sub prop
      where
        Just sub = unifyList (buildList (map fst cs)) (buildList (map snd cs))
        cs = [(fst x, fst y) | x:xs <- vs, y <- xs] ++ concatMap litCs (lhs prop) ++ litCs (rhs prop)
        vs = partitionBy fst (concatMap typedVars (propTerms prop))
    litCs (t :=: u) = [(typ t, typ u)] ++ termCs t ++ termCs u
    litCs (p :@: ts) = [(typ p, arrowType (map typ ts) (typeOf True))] ++ concatMap termCs ts
    termCs Var{} = []
    termCs (App (Id _) [Var _]) = []
    termCs t@(App f ts) = [(typ f, arrowType (map typ ts) (typ t))] ++ concatMap termCs ts
