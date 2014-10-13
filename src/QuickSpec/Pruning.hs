{-# LANGUAGE CPP #-}
module QuickSpec.Pruning where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Test
import QuickSpec.Utils
import QuickSpec.Signature
import QuickSpec.Equation
import Control.Monad.Trans.State.Strict
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Rewriting.Substitution.Type
import Data.Maybe

class Pruner a where
  untypedEmptyPruner :: a
  unifyUntyped :: PruningTerm -> PruningTerm -> State a Bool
  repUntyped :: PruningTerm -> State a (Maybe PruningTerm)

emptyPruner :: Pruner a => Set Type -> Signature -> a
emptyPruner univ sig = execState go untypedEmptyPruner
  where
    go = mapM_ axiom (constants sig >>= partiallyApply >>= instances >>= return . oneTypeVar)
    axiom t = unifyUntyped (Fun (HasType (typ t)) [toPruningTerm t]) (toPruningTerm t)
    instances t@(Fun _ ts) =
      [ typeSubst (evalSubst (fromMap sub)) t
      | sub <- foldr intersection [Map.empty] (map (constrain (Set.toList univ)) (t:ts)) ]
    partiallyApply x =
      [ fun (Fun x []) ts
      | i <- [0..conArity x],
        let ts = [ Var (Variable j (Var (TyVar 0))) | j <- [0..i-1] ] ]
    fun x [] = x
    fun x (t:ts) = fun (unPoly (poly x `apply` poly t)) ts

unify :: Pruner a => Set Type -> Equation -> State a Bool
unify univ e = do
  let e' = unifyEquation e
  res <- unifyOne (lhs e', rhs e')
  case res of
    True ->
      return True
    False -> do
      mapM_ unifyOne (eqnInstances (Set.toList univ) (lhs e') (rhs e'))
      return False

toPruningEquation :: Equation -> (PruningTerm, PruningTerm)
toPruningEquation e = (toPruningTerm (lhs e'), toPruningTerm (rhs e'))
  where
    e' = unifyEquation e

unifyEquation :: Equation -> Equation
unifyEquation (lhs :=: rhs) = lhs' :=: rhs'
  where
    Just ty = polyMgu (poly (typ lhs)) (poly (typ rhs))
    Just lhs' = cast (unPoly ty) lhs
    Just rhs' = cast (unPoly ty) rhs

eqnInstances :: [Type] -> Term -> Term -> [(Term, Term)]
eqnInstances univ lhs rhs =
  [ (lhs', rhs')
  | sub <- map fromMap cs,
    let lhs' = typeSubst (evalSubst sub) lhs,
    let rhs' = typeSubst (evalSubst sub) rhs ]
  where
    cs =
      foldr intersection [Map.empty]
        (map (constrain univ)
          (concatMap subterms [lhs, rhs]))

intersection :: [Map TyVar Type] -> [Map TyVar Type] -> [Map TyVar Type]
ms1 `intersection` ms2 = usort [ Map.union m1 m2 | m1 <- ms1, m2 <- ms2, ok m1 m2 ]
  where
    ok m1 m2 = and [ Map.lookup x m1 == Map.lookup x m2 | x <- Map.keys (Map.intersection m1 m2) ]

constrain :: Typed a => [Type] -> a -> [Map TyVar Type]
constrain univ t =
  usort [ toMap sub | u <- univ, Just sub <- [match (typ t) u] ]

unifyOne :: Pruner a => (Term, Term) -> State a Bool
unifyOne (lhs, rhs) = unifyUntyped (toPruningTerm lhs) (toPruningTerm rhs)

rep :: Pruner a => Term -> State a (Maybe Term)
rep t = fmap (fmap fromPruningTerm) (repUntyped (toPruningTerm t))

type PruningTerm = Tm PruningConstant PruningVariable

data PruningConstant
  -- Invariant: type is constant's monotype
  = TermConstant Constant Int Type
  | HasType Type
  deriving (Eq, Ord, Show)

instance Pretty PruningConstant where
  pretty (TermConstant x _ ty) = pretty x
  pretty (HasType ty) = text "@" <> pretty ty

data PruningVariable
  -- Invariant: type is variable's monotype
  = TermVariable Variable Type
  deriving (Eq, Ord, Show)

instance Pretty PruningVariable where
  pretty (TermVariable x ty) = pretty x

toPruningTerm :: Term -> PruningTerm
toPruningTerm = guardNakedVariables . go
  where
    go (Fun f xs) = Fun (TermConstant f (length xs) (typ (oneTypeVar f))) (map go xs)
    go (Var x) = Var (TermVariable x (typ (oneTypeVar x)))
    guardNakedVariables x@(Var (TermVariable _ ty)) = Fun (HasType ty) [x]
    guardNakedVariables x = x

-- FIXME not sure this is right!
fromPruningTerm :: PruningTerm -> Term
fromPruningTerm (Var (TermVariable x _)) = Var x
fromPruningTerm (Fun (TermConstant f _ _) xs) = Fun f (map fromPruningTerm xs)
fromPruningTerm (Fun (HasType _) [x]) = fromPruningTerm x
