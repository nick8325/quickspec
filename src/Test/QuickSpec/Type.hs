-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types #-}
-- To avoid a warning about TyVarNumber's constructor being unused:
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module Test.QuickSpec.Type(
  -- Types.
  Typeable,
  Type, TyCon(..), TyVar(..), arrowType,
  TyVars(..), Typed(..), typeSubst, freshTyVarFor, freshen,
  UnifyM, runUnifyM, equalise, freshTyVar,
  tryApply, canApply, apply,
  A, B, C, D,
  typeOf,
  fromTypeRep,
  toTypeRep,
  -- Dynamic values.
  Value,
  toValue,
  fromValue,
  valueType,
  mapValue,
  pairValues) where

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
import Data.Ord
import qualified Data.DList as DList
import Data.DList(DList)
import Data.Functor.Identity

-- A (possibly polymorphic) type.
type Type = Tm TyCon TyVar

data TyCon = Arrow | TyCon Ty.TyCon deriving (Eq, Ord, Show)
newtype TyVar = TyVar { tyVarNumber :: Int } deriving (Eq, Ord, Show, Enum)

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

-- Things that contain types (e.g., contexts).
class TyVars a where
  -- Substitute for all type variables.
  typeSubstA :: Applicative f => (TyVar -> f Type) -> a -> f a

-- Typed things that support function application.
class TyVars a => Typed a where
  -- Generate the constraints needed to apply a function to its argument.
  adapt :: a -> a -> UnifyM ()

  -- Apply a function to its argument, assuming that equalise has already
  -- been used to unify the relevant bits of the types.
  groundApply :: a -> a -> a

typeSubst :: TyVars a => (TyVar -> Type) -> a -> a
typeSubst f t = runIdentity (typeSubstA (return . f) t)

freshTyVarFor :: TyVars a => a -> TyVar
freshTyVarFor t =
  case execWriter (typeSubstA (\x -> do { tell (Max (Just x)); return (Var x) }) t) of
    Max Nothing -> TyVar 0
    Max (Just (TyVar n)) -> TyVar (n+1)

freshen :: TyVars a => TyVar -> a -> a
freshen (TyVar x) t = typeSubst (\(TyVar n) -> Var (TyVar (n+x))) t

-- A monad for generating unification constraints.
type UnifyM = StateT TyVar (WriterT (DList (Type, Type)) Maybe)

runUnifyM :: UnifyM a -> TyVar -> Maybe (a, Subst TyCon TyVar)
runUnifyM x tv = do
  (x, cs) <- runWriterT (evalStateT x tv)
  s <- unifyMany Arrow (DList.toList cs)
  return (x, s)

freshTyVar :: UnifyM TyVar
freshTyVar = do
  tv <- get
  put $! succ tv
  return tv

equalise :: Type -> Type -> UnifyM ()
equalise t u = lift (tell (DList.singleton (t, u)))

-- Application of typed terms.
tryApply :: Typed a => a -> a -> Maybe a
tryApply f x = do
  let tv = freshTyVarFor f
      x' = freshen tv x
      tv' = freshTyVarFor x' `max` tv
  ((), s) <- runUnifyM (adapt f x') tv'
  let sub = typeSubst (evalSubst s)
  return (sub f `groundApply` sub x')

infixl `apply`
apply :: Typed a => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing -> ERROR "apply: ill-typed term"
    Just y -> y

canApply :: Typed a => a -> a -> Bool
canApply f x = isJust (tryApply f x)

instance TyVars Type where
  typeSubstA = substA
instance Typed Type where
  adapt t u = do
    tv <- freshTyVar
    equalise t (Fun Arrow [u, Var tv])
  groundApply (Fun Arrow [arg, res]) t | t == arg = res

-- Dynamic values inside an applicative functor.
data Value f =
  Value {
    valueType :: Type,
    value :: f Any }

instance Show (Value f) where
  show x = "<<" ++ show (toTypeRep (valueType x)) ++ ">>"

fromAny :: f Any -> f a
fromAny = unsafeCoerce

toAny :: f a -> f Any
toAny = unsafeCoerce

toValue :: forall f a. Typeable a => f a -> Value f
toValue x = Value (typeOf (undefined :: a)) (toAny x)

instance TyVars (Value f) where
  typeSubstA f (Value ty x) = Value <$> typeSubstA f ty <*> pure x
instance Applicative f => Typed (Value f) where
  adapt f x = adapt (valueType f) (valueType x)
  groundApply f x =
    -- Use $! to check that the types match before computing the value
    (Value $! groundApply (valueType f) (valueType x))
    (fromAny (value f) <*> value x)

fromValue :: forall f a. Typeable a => Value f -> Maybe (f a)
fromValue x = do
  let ty = typeOf (undefined :: a)
  _ <- match (valueType x) ty
  return (fromAny (value x))

mapValue :: (forall a. f a -> g a) -> Value f -> Value g
mapValue f (Value ty x) = Value ty (f x)

pairValues :: (forall a. f a -> g a -> h a) -> Value f -> Value g -> Maybe (Value h)
pairValues f x y = do
  let y' = freshen (freshTyVarFor x) y
  s <- unify (valueType x) (valueType y')
  let z = subst s (valueType x)
  return (Value z (f (value x) (value y)))
