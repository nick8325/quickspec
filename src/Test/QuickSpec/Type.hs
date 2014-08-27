-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls #-}
module Test.QuickSpec.Type(
  -- Types.
  Typeable,
  Type, TyCon(..),
  typeOf,
  fromTypeRep,
  toTypeRep,
  applyType,
  -- Dynamic values.
  Value,
  toValue,
  fromValue,
  typeOfValue,
  apply, tryApply)
  where

#include "errors.h"

import Data.Rewriting.Term hiding (map)
import Data.Rewriting.Substitution hiding (apply)
import qualified Data.Rewriting.Substitution as T
import Data.Typeable(Typeable)
import qualified Data.Typeable as Ty
import GHC.Exts(Any)
import Unsafe.Coerce
import Control.Applicative

-- A (possibly polymorphic) type.
type Type = Term TyCon Int
data TyCon = Arrow | TyCon Ty.TyCon deriving (Eq, Ord, Show)

-- Type variables.
type A = TyVar Zero
type B = TyVar (Succ Zero)
type C = TyVar (Succ (Succ Zero))
type D = TyVar (Succ (Succ (Succ Zero)))
newtype TyVar a = TyVar Any deriving Typeable
data Zero deriving Typeable
data Succ a deriving Typeable

typeOf :: Typeable a => a -> Type
typeOf x = fromTypeRep (Ty.typeOf x)

fromTypeRep :: Ty.TypeRep -> Type
fromTypeRep ty =
  case Ty.splitTyConApp ty of
    (tyVar, [ty]) | tyVar == varTyCon -> Var (fromTyVar ty)
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
varTyCon   = con (undefined :: TyVar ())
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
toTypeRep (Var n) = Ty.mkTyConApp varTyCon [toTyVar n]
  where
    toTyVar 0 = Ty.mkTyConApp zeroTyCon []
    toTyVar n = Ty.mkTyConApp succTyCon [toTyVar (n-1)]

-- Dynamic values inside an applicative functor.
data Value f = Value {
  typeOfValue :: Type,
  value :: f Any
  }

instance Show (Value f) where
  show x = show (toTypeRep (typeOfValue x))

fromAny :: Any -> a
fromAny = unsafeCoerce

toAny :: a -> Any
toAny = unsafeCoerce

toValue :: forall f a. (Typeable a, Typeable f, Applicative f) => f a -> Value f
toValue x = Value (typeOf (undefined :: a)) (fmap toAny x)

apply :: Applicative f => Value f -> Value f -> Value f
apply f x =
  case tryApply f x of
    Nothing -> ERROR "apply: incompatible types"
    Just y -> y

tryApply :: Applicative f => Value f -> Value f -> Maybe (Value f)
tryApply f x = do
  y <- applyType (typeOfValue f) (typeOfValue x)
  return (Value y (applyValue f x))

applyType :: Type -> Type -> Maybe Type
-- Common case: monomorphic application
applyType (Fun Arrow [t, u]) v | t == v = Just u
-- Polymorphic application
applyType (Fun Arrow [arg, res]) t = do
  s <- unify arg (freshen arg t)
  return (T.apply s res)
-- Rare case: type variable
applyType (Var _) t = Just t
applyType _ _ = Nothing

-- Rename a type so as to make its variables not clash with another type
freshen t u = rename (n+) u
  where
    n = maximum (0:vars t)

applyValue :: Applicative f => Value f -> Value f -> f Any
applyValue f x = fmap fromAny (value f) <*> value x

fromValue :: forall f a. (Typeable a, Applicative f) => Value f -> Maybe (f a)
fromValue x = do
  let ty = typeOf (undefined :: a)
  _ <- match (typeOfValue x) ty
  return (fmap fromAny (value x))
