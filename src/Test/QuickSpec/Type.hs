-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances #-}
module Test.QuickSpec.Type(
  -- Types.
  Typeable,
  Apply(..),
  Type, TyCon(..), TyVar(..),
  typeOf,
  fromTypeRep,
  toTypeRep,
  -- Dynamic values.
  Value,
  toValue,
  fromValue,
  typeOfValue)
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
import Data.Maybe

-- A (possibly polymorphic) type.
type Type = Term TyCon TyVar
data TyCon = Arrow | TyCon Ty.TyCon deriving (Eq, Ord, Show)
newtype TyVar = TyVar { tyVarNumber :: Int } deriving (Eq, Ord, Show)

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

-- Dynamic values inside an applicative functor.
data Value f = Value {
  typeOfValue :: Type,
  value :: f Any
  }

instance Show (Value f) where
  show x = show (toTypeRep (typeOfValue x))

fromAny :: f Any -> f a
fromAny = unsafeCoerce

toAny :: f a -> f Any
toAny = unsafeCoerce

toValue :: forall f a. Typeable a => f a -> Value f
toValue x = Value (typeOf (undefined :: a)) (toAny x)

class Apply a where
  tryApply :: a -> a -> Maybe a

apply :: Apply a => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing -> ERROR "apply: ill-typed term"
    Just y -> y

canApply :: Apply a => a -> a -> Bool
canApply f x = isJust (tryApply f x)

instance Applicative f => Apply (Value f) where
  tryApply f x = do
    y <- tryApply (typeOfValue f) (typeOfValue x)
    return (Value y (fromAny (value f) <*> value x))

instance Apply Type where
  -- Common case: monomorphic application
  tryApply (Fun Arrow [t, u]) v | t == v = Just u
  -- Polymorphic application
  tryApply (Fun Arrow [arg, res]) t = do
    s <- unify arg (freshen arg t)
    return (T.apply s res)
  -- Rare case: type variable
  tryApply (Var _) t = Just t
  tryApply _ _ = Nothing

-- Rename a type so as to make its variables not clash with another type
freshen t u = rename (TyVar . (n+) . tyVarNumber) u
  where
    n = maximum (0:map tyVarNumber (vars t))

fromValue :: forall f a. Typeable a => Value f -> Maybe (f a)
fromValue x = do
  let ty = typeOf (undefined :: a)
  _ <- match (typeOfValue x) ty
  return (fromAny (value x))
