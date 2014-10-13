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
  repUntyped         :: PruningTerm -> State a (Maybe PruningTerm)
  areEqualUntyped    :: PruningTerm -> PruningTerm -> State a Bool
  unifyUntyped       :: PruningTerm -> PruningTerm -> State a ()

emptyPruner :: Pruner a => Set Type -> Signature -> a
emptyPruner univ sig = execState go untypedEmptyPruner
  where
    go = do
      mapM_ axiom (constants sig >>= partiallyApply >>= instances >>= return . oneTypeVar)
      mapM_ typeAxiom (Set.toList univ)
    axiom t = unifyUntyped (Fun (HasType (typ t)) [normaliseVars (toPruningTerm t)]) (normaliseVars (toPruningTerm t))
    -- Since we don't add any type axioms for skolem variables,
    -- we might need type axioms for HasType, I'm not sure.
    typeAxiom ty = unifyUntyped (hasTy (hasTy (Var 0))) (hasTy (Var 0))
      where
        hasTy t = Fun (HasType ty) [t]
    instances t@(Fun _ ts) =
      [ typeSubst (evalSubst (fromMap sub)) t
      | sub <- foldr intersection [Map.empty] (map (constrain (Set.toList univ)) (t:ts)) ]
    partiallyApply x =
      [ fun (Fun x []) ts
      | i <- [0..conArity x],
        let ts = [ Var (Variable j (Var (TyVar 0))) | j <- [0..i-1] ] ]
    fun x [] = x
    fun x (t:ts) = fun (unPoly (poly x `apply` poly t)) ts

unify :: Pruner a => Set Type -> Equation -> State a ()
unify univ e =
  sequence_
    [ unifyUntyped t' u'
    | (lhs, rhs) <- eqnInstances (Set.toList univ) (lhs e') (rhs e'),
      let t = toPruningTerm lhs,
      let u = toPruningTerm rhs,
      let (t', u') = normaliseEquation (t, u) ]
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

constrain :: [Type] -> Term -> [Map TyVar Type]
constrain univ t =
  usort [ toMap sub | u <- univ, Just sub <- [match (typ t) u] ]

rep :: Pruner a => Term -> State a (Maybe Term)
rep t = fmap (fmap fromPruningTerm) (repUntyped (normaliseVars (toPruningTerm t)))

type PruningTerm = Tm PruningConstant Int

data PruningConstant
  = TermConstant Constant Type Int
    -- The type is always the same as the constant's type,
    -- it's only included here so that it's counted in the Ord instance
  | SkolemVariable Variable
  | HasType Type
  deriving (Eq, Ord, Show)

instance Pretty PruningConstant where
  pretty (TermConstant x _ _) = pretty x
  pretty (HasType ty) = text "@" <> pretty ty

toPruningTerm :: Term -> Tm PruningConstant Variable
toPruningTerm = toPruningTerm2 . toPruningTerm1
toPruningTermSkolem :: Term -> PruningTerm
toPruningTermSkolem = normaliseVars . toPruningTerm2 . skolemise . toPruningTerm1
  where
    skolemise (Fun f xs) = Fun f (map skolemise xs)
    skolemise (Var x) = Fun (HasType (typ x)) [Fun (SkolemVariable x) []]

toPruningTerm1 :: Term -> Tm PruningConstant Variable
toPruningTerm1 = mapTerm f id . withArity
  where
    f (fun, n) = TermConstant fun (typ fun) n

toPruningTerm2 :: Tm PruningConstant Variable -> Tm PruningConstant Variable
toPruningTerm2 = guardNakedVariables
  where
    guardNakedVariables (Var x) = Fun (HasType (typ x)) [Var x]
    guardNakedVariables x = x

fromPruningTerm :: PruningTerm -> Term
fromPruningTerm t =
  fromPruningTermWith n t
  where
    n = maximum (0:[1+n | SkolemVariable (Variable n _) <- funs t])

fromPruningTermWith :: Int -> PruningTerm -> Term
fromPruningTermWith n (Fun (TermConstant fun _ _) xs) =
  Fun fun (zipWith (fromPruningTermWithType n) (typeArgs (typ fun)) xs)
fromPruningTermWith n (Fun (HasType ty) [t]) = fromPruningTermWithType n ty t
fromPruningTermWith _ _ = ERROR "ill-typed term?"

fromPruningTermWithType :: Int -> Type -> PruningTerm -> Term
fromPruningTermWithType m ty (Var n) = Var (Variable (m+n) ty)
fromPruningTermWithType n ty (Fun (SkolemVariable x) []) = Var x
fromPruningTermWithType n _  t = fromPruningTermWith n t

normaliseVars t = rename (\x -> fromMaybe __ (Map.lookup x m)) t
  where
    m = Map.fromList (zip (usort (vars t)) [0..])

normaliseEquation (t, u) =
  (rename (\x -> fromMaybe __ (Map.lookup x m)) t,
   rename (\x -> fromMaybe __ (Map.lookup x m)) u)
  where
    m = Map.fromList (zip (usort (vars t ++ vars u)) [0..])
