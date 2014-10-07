-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, ExistentialQuantification #-}
-- To avoid a warning about TyVarNumber's constructor being unused:
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module Test.QuickSpec.Type(
  -- Types.
  Typeable,
  Type, TyCon(..), TyVar(..), arrowType, arity,
  Typed(..), Apply(..), typeSubst, freshTyVarFor, freshen, tyVars,
  UnifyM, runUnifyM, execUnifyM, equalise, freshTyVar, freshenM,
  tryApply, canApply, apply,
  A, B, C, D,
  typeOf,
  fromTypeRep,
  toTypeRep,
  -- Dynamic values.
  Value,
  toValue,
  fromValue,
  castValue,
  ofValue,
  mapValue,
  forValue,
  pairValues,
  Poly, poly, unPoly,
  Unwrapped(..), unwrap) where

#include "errors.h"

import Test.QuickSpec.Base
import Test.QuickSpec.Utils
import Data.Typeable(Typeable)
import qualified Data.Typeable as Ty
import GHC.Exts(Any)
import Unsafe.Coerce
import Control.Applicative
import Data.Maybe
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import qualified Data.DList as DList
import Data.DList(DList)
import Data.Functor.Identity
import Data.Traversable(traverse)
import qualified Data.Map as Map
import qualified Data.Rewriting.Substitution.Type as T
import Data.List

-- A (possibly polymorphic) type.
type Type = Tm TyCon TyVar

data TyCon = Arrow | TyCon Ty.TyCon deriving (Eq, Ord, Show)
newtype TyVar = TyVar { tyVarNumber :: Int } deriving (Eq, Ord, Show, Enum)

instance Pretty TyCon where
  pretty Arrow = text "->"
  pretty (TyCon x) = text (show x)
instance Pretty TyVar where
  pretty (TyVar n) = text ("a" ++ show n)

-- Type variables.
type A = TyVarNumber Zero
type B = TyVarNumber (Succ Zero)
type C = TyVarNumber (Succ (Succ Zero))
type D = TyVarNumber (Succ (Succ (Succ Zero)))
newtype TyVarNumber a = TyVarNumber Any deriving Typeable
data Zero deriving Typeable
data Succ a deriving Typeable

typeOf :: Typeable a => a -> Type
typeOf x = fromTypeRep (Ty.typeOf x)

arrowType :: [Type] -> Type -> Type
arrowType [] res = res
arrowType (arg:args) res = Fun Arrow [arg, arrowType args res]

arity :: Type -> Int
arity (Fun Arrow [_, res]) = 1+arity res
arity _ = 0

fromTypeRep :: Ty.TypeRep -> Type
fromTypeRep ty =
  case Ty.splitTyConApp ty of
    (tyVar, [ty]) | tyVar == varTyCon -> Var (TyVar (fromTyVar ty))
    (tyCon, tys) -> Fun (fromTyCon tyCon) (map fromTypeRep tys)
  where
    fromTyCon tyCon
      | tyCon == arrowTyCon = Arrow
      | otherwise = TyCon tyCon
    fromTyVar ty =
      case Ty.splitTyConApp ty of
        (tyCon, [ty']) | tyCon == succTyCon -> succ (fromTyVar ty')
        (tyCon, []) | tyCon == zeroTyCon -> 0

arrowTyCon, varTyCon, succTyCon, zeroTyCon :: Ty.TyCon
arrowTyCon = con (undefined :: () -> ())
varTyCon   = con (undefined :: TyVarNumber ())
succTyCon  = con (undefined :: Succ ())
zeroTyCon  = con (undefined :: Zero)

con :: Typeable a => a -> Ty.TyCon
con = fst . Ty.splitTyConApp . Ty.typeOf

-- Mostly for showing types.
toTypeRep :: Type -> Ty.TypeRep
toTypeRep (Fun tyCon tys) = Ty.mkTyConApp (toTyCon tyCon) (map toTypeRep tys)
  where
    toTyCon Arrow = arrowTyCon
    toTyCon (TyCon tyCon) = tyCon
toTypeRep (Var (TyVar n)) = Ty.mkTyConApp varTyCon [toTyVar n]
  where
    toTyVar 0 = Ty.mkTyConApp zeroTyCon []
    toTyVar n = Ty.mkTyConApp succTyCon [toTyVar (n-1)]

-- Things with types.
class Typed a where
  -- The type.
  typ :: a -> Type
  -- Substitute for all type variables.
  typeSubstA :: Applicative f => (TyVar -> f Type) -> a -> f a

-- Typed things that support function application.
class Typed a => Apply a where
  -- Generate the constraints needed to apply a function to its argument.
  adapt :: a -> a -> UnifyM ()
  adapt t u = adapt (typ t) (typ u)

  -- Apply a function to its argument, assuming that equalise has already
  -- been used to unify the relevant bits of the types.
  groundApply :: a -> a -> a

typeSubst :: Typed a => (TyVar -> Type) -> a -> a
typeSubst f t = runIdentity (typeSubstA (return . f) t)

tyVars :: Typed a => a -> [TyVar]
tyVars t = DList.toList (execWriter (typeSubstA f t))
  where
    f x = do
      tell (DList.singleton x)
      return (Var x)

freshTyVarFor :: Typed a => a -> TyVar
freshTyVarFor t =
  case execWriter (typeSubstA (\x -> do { tell (Max (Just x)); return (Var x) }) t) of
    Max Nothing -> TyVar 0
    Max (Just (TyVar n)) -> TyVar (n+1)

freshen :: Typed a => TyVar -> a -> a
freshen (TyVar x) t = typeSubst (\(TyVar n) -> Var (TyVar (n+x))) t

freshenM :: Typed a => a -> UnifyM a
freshenM t = do
  let TyVar n = freshTyVarFor t
  tv <- freshTyped n
  return (freshen tv t)

-- A monad for generating unification constraints.
type UnifyM = StateT TyVar (WriterT (DList (Type, Type)) Maybe)

runUnifyM :: TyVar -> UnifyM a -> Maybe (a, Subst TyCon TyVar)
runUnifyM tv x = do
  (x, cs) <- runWriterT (evalStateT x tv)
  s <- unifyMany Arrow (DList.toList cs)
  return (x, s)

execUnifyM :: TyVar -> UnifyM a -> Maybe (Subst TyCon TyVar)
execUnifyM tv x = fmap snd (runUnifyM tv x)

freshTyVar :: UnifyM TyVar
freshTyVar = freshTyped 1

freshTyped :: Int -> UnifyM TyVar
freshTyped n = do
  tv@(TyVar m) <- get
  put $! TyVar (m+n)
  return tv

equalise :: Type -> Type -> UnifyM ()
equalise t u = lift (tell (DList.singleton (t, u)))

-- Application of typed terms.
tryApply :: Apply a => a -> a -> Maybe a
tryApply f x = do
  let tv = freshTyVarFor f
      x' = freshen tv x
      tv' = freshTyVarFor x' `max` tv
  s <- execUnifyM tv' (adapt f x')
  let sub = typeSubst (evalSubst s)
  return (sub f `groundApply` sub x')

infixl `apply`
apply :: Apply a => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing -> ERROR "apply: ill-typed term"
    Just y -> y

canApply :: Apply a => a -> a -> Bool
canApply f x = isJust (tryApply f x)

instance Typed Type where
  typ = id
  typeSubstA s (Var x) = s x
  typeSubstA s (Fun f xs) =
    Fun f <$> traverse (typeSubstA s) xs

instance Apply Type where
  adapt t u = do
    tv <- freshTyVar
    equalise t (Fun Arrow [u, Var tv])
  groundApply (Fun Arrow [arg, res]) t | t == arg = res
  groundApply t u = ERROR ("Incompatible function types " ++ prettyShow t ++ " and " ++ prettyShow u)

-- Dynamic values inside an applicative functor.
data Value f =
  Value {
    valueType :: Type,
    value :: f Any }

instance Show (Value f) where
  show x = "<<" ++ prettyShow (valueType x) ++ ">>"

fromAny :: f Any -> f a
fromAny = unsafeCoerce

toAny :: f a -> f Any
toAny = unsafeCoerce

toValue :: forall f a. Typeable a => f a -> Value f
toValue x = Value (typeOf (undefined :: a)) (toAny x)

instance Typed (Value f) where
  typ = valueType
  typeSubstA f (Value ty x) = Value <$> typeSubstA f ty <*> pure x
instance Applicative f => Apply (Value f) where
  groundApply f x =
    -- Use $! to check that the types match before computing the value
    (Value $! groundApply (valueType f) (valueType x))
    (fromAny (value f) <*> value x)

castValue :: forall f. Type -> Value f -> Maybe (Value f)
castValue ty x = do
  s <- match (valueType x) ty
  return x { valueType = typeSubst (evalSubst s) (valueType x) }

fromValue :: forall f a. Typeable a => Value f -> Maybe (f a)
fromValue x = do
  _ <- castValue (typeOf (undefined :: a)) x
  return (fromAny (value x))

mapValue :: (forall a. f a -> g a) -> Value f -> Value g
mapValue f v =
  case unwrap v of
    U x wrap -> wrap (f x)

forValue :: Value f -> (forall a. f a -> g a) -> Value g
forValue x f = mapValue f x

ofValue :: (forall a. f a -> b) -> Value f -> b
ofValue f v =
  case unwrap v of
    U x _ -> f x

pairValues :: (forall a. f a -> g a -> h a) -> Value f -> Value g -> Maybe (Value h)
pairValues f x y = do
  let y' = freshen (freshTyVarFor x) y
  s <- unify (valueType x) (valueType y')
  let z = subst s (valueType x)
  return (Value z (f (value x) (value y)))

-- Represents a forall-quantifier over all the type variables in a type.
-- Wrapping a term in Poly normalises the type by alpha-renaming
-- type variables canonically.
newtype Poly a = Poly { unPoly :: a }
  deriving (Eq, Ord, Show, Pretty, Typeable)

poly :: Typed a => a -> Poly a
poly = Poly . normaliseType

normaliseType :: Typed a => a -> a
normaliseType t = typeSubst (evalSubst s) t
  where
    s = T.fromMap (Map.fromList (zip tvs (map (Var . TyVar) [0..])))
    tvs = tvs' ++ (usort (tyVars t) \\ tvs')
    tvs' = usort (tyVars (typ t))

data Unwrapped f = forall a. U (f a) (forall g. g a -> Value g)

unwrap :: Value f -> Unwrapped f
unwrap x = U (value x) (\y -> Value (typ x) y)
