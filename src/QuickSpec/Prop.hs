{-# LANGUAGE DeriveFunctor, CPP, TypeFamilies, FlexibleContexts, BangPatterns #-}
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
  pPrintPrec _ _ (x :=: y) = hang (pPrint x <+> text "=") 2 (pPrint y)
  pPrintPrec l p (pred :@: xs) =
    pPrintTerm (termStyle pred) l p (pPrint pred) xs

data Predicate = Predicate {
  predName  :: String,
  predStyle :: TermStyle,
  predType  :: Type,
  predGeneralType :: Poly Type }

instance Eq Predicate where
  p == q = p `compare` q == EQ

instance Ord Predicate where
  compare = comparing f
    where
      f p = (predName p, predType p, predGeneralType p)

instance Show Predicate where
  show = prettyShow

instance Pretty Predicate where
  pPrint = text . predName

instance PrettyTerm Predicate where
  termStyle = predStyle

instance Typed Predicate where
  typ = predType
  typeReplace sub (Predicate x style ty pty) = Predicate x style (typeReplace sub ty) pty

boolType :: Type
boolType = typeOf (undefined :: Bool)

-- Given a property which only contains one type variable,
-- add as much polymorphism to the property as possible.
-- e.g.    map (f :: a -> a) (xs++ys) = map f xs++map f ys
-- becomes map (f :: a -> b) (xs++ys) = map f xs++map f ys.
regeneralise :: Prop -> Prop
regeneralise =
  -- First replace each type variable occurrence with a fresh
  -- type variable (generalise), then unify type variables
  -- where necessary to preserve well-typedness (restrict).
  restrict . unPoly . generalise . canonicalise
  where
    generalise (lhs :=>: rhs) =
      polyApply (:=>:) (polyList (map genLit lhs)) (genLit rhs)
    genLit (p :@: ts) =
      polyApply (:@:) (genPred p) (polyList (map genTerm ts))
    genLit (t :=: u) = polyApply (:=:) (genTerm t) (genTerm u)
    genTerm (App (Id ty) [x@Var{}]) =
      polyMap (\ty -> app (Id ty) [x]) (genType ty)
    genTerm (App f ts) =
      polyApply app (genCon f) (polyList (map genTerm ts))

    -- We change the type of a constant f to the mgu of:
    --   * f's most polymorphic type, and
    --   * f's type with all type variables replaced by fresh ones
    genPred p = poly (genTyped (typ p) p { predType = unPoly (predGeneralType p) })
    genCon f@(Apply _) = poly (genTyped (typ f) (Apply (build (var (MkVar 0)))))
    genCon f = poly (genTyped (typ f) f { conValue = unPoly (conGeneralValue f) })

    genTyped :: Typed a => Type -> a -> a
    genTyped ty x =
      let
        (ty', x') = unPoly (polyPair (genType ty) (poly x))
        Just sub = unify ty' (typ x')
      in typeSubst sub x'

    genType = poly . build . aux 0 . singleton
      where
        aux !_ Empty = mempty
        aux n (Cons (Var _) ts) =
          var (MkVar n) `mappend` aux (n+1) ts
        aux n (Cons (Fun f ts) us) =
          fun f (aux n ts) `mappend`
          aux (n+lenList ts) us

    restrict prop = typeSubst sub prop
      where
        Just sub = unifyList (buildList (map fst cs)) (buildList (map snd cs))
        cs = [(fst x, fst y) | x:xs <- vs, y <- xs] ++ concatMap litCs (lhs prop) ++ litCs (rhs prop)
        -- Two variables that were equal before generalisation must have the
        -- same type afterwards
        vs = partitionBy skel (concatMap typedVars (propTerms prop))
        skel (ty, x) = (subst (const (var (MkVar 0))) ty, x)
    litCs (t :=: u) = [(typ t, typ u)] ++ termCs t ++ termCs u
    litCs (p :@: ts) = [(typ p, arrowType (map typ ts) (typeOf True))] ++ concatMap termCs ts
    termCs Var{} = []
    termCs (App (Id _) [Var _]) = []
    termCs t@(App f ts) = [(typ f, arrowType (map typ ts) (typ t))] ++ concatMap termCs ts
