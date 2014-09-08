-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types #-}
module Test.QuickSpec.Type(
  -- Types.
  Typeable,
  Type, TyCon(..), TyVar(..),
  TyVars(..), freshTyVar,
  Apply(..), tryApply, canApply, apply,
  A, B, C, D,
  typeOf,
  fromTypeRep,
  toTypeRep,
  -- Dynamic values.
  Value,
  toValue,
  fromValue,
  typeOfValue,
  injectValue) where

#include "errors.h"

import Test.QuickSpec.Base
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

-- Typechecking applications.
class TyVars a where
  tyVars :: a -> [TyVar]
  tySubst :: (TyVar -> Type) -> a -> a

instance TyVars Type where
  tyVars = vars
  tySubst = subst'

instance TyVars a => TyVars [a] where
  tyVars xs = concatMap tyVars xs
  tySubst f xs = map (tySubst f) xs

instance (TyVars a, TyVars b) => TyVars (a, b) where
  tyVars (x, y) = tyVars x ++ tyVars y
  tySubst f (x, y) = (tySubst f x, tySubst f y)

class TyVars a => Apply a where
  tyApply :: a -> a -> ApplyM (a, a)
  tyGroundApply :: a -> a -> a

type ApplyM = StateT TyVar (WriterT [(Type, Type)] Maybe)
evalApply :: ApplyM a -> TyVar -> Maybe (a, [(Type, Type)])
evalApply x tv = runWriterT (evalStateT x tv)
freshTyVar :: ApplyM TyVar
freshTyVar = do
  tv <- get
  put $! succ tv
  return tv

instance Apply Type where
  tyApply t u = do
    tv <- freshTyVar
    lift (tell [(t, Fun Arrow [u, Var tv])])
    return (t, u)
  tyGroundApply (Fun Arrow [arg, res]) t | t == arg = res

freshTyVarFor :: Apply a => a -> TyVar
freshTyVarFor x = TyVar (1+n)
  where
    n = maximum (0:map tyVarNumber (tyVars x))

tryApply :: Apply a => a -> a -> Maybe a
tryApply f x = do
  let TyVar n = freshTyVarFor f
      x' = tySubst (Var . TyVar . (n+1+) . tyVarNumber) x
      TyVar m = freshTyVarFor x'
      tv = TyVar (m `max` n)
  ((f', x''), cs) <- evalApply (tyApply f x') tv
  s <- unifyMany Arrow cs
  let sub = tySubst (subst s . Var)
  return (sub f' `tyGroundApply` sub x'')

infixl `apply`
apply :: Apply a => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing -> ERROR "apply: ill-typed term"
    Just y -> y

canApply :: Apply a => a -> a -> Bool
canApply f x = isJust (tryApply f x)

-- Dynamic values inside an applicative functor.
data Value f =
  Value {
    typeOfValue :: Type,
    value :: f Any }

-- XXX this is convenient for term generation, but is it too dangerous?
instance Eq (Value f) where
  x == y = x `compare` y == EQ
instance Ord (Value f) where
  compare = comparing typeOfValue

instance Show (Value f) where
  show x = "<<" ++ show (toTypeRep (typeOfValue x)) ++ ">>"

fromAny :: f Any -> f a
fromAny = unsafeCoerce

toAny :: f a -> f Any
toAny = unsafeCoerce

toValue :: forall f a. Typeable a => f a -> Value f
toValue x = Value (typeOf (undefined :: a)) (toAny x)

instance TyVars (Value f) where
  tyVars = tyVars . typeOfValue
  tySubst f x = x { typeOfValue = tySubst f (typeOfValue x) }

instance Applicative f => Apply (Value f) where
  tyApply f x = do
    (f', x') <- tyApply (typeOfValue f) (typeOfValue x)
    return (f { typeOfValue = f' }, x { typeOfValue = x' })
  tyGroundApply f x =
    (Value $! tyGroundApply (typeOfValue f) (typeOfValue x))
    (fromAny (value f) <*> value x)

fromValue :: forall f a. Typeable a => Value f -> Maybe (f a)
fromValue x = do
  let ty = typeOf (undefined :: a)
  _ <- match (typeOfValue x) ty
  return (fromAny (value x))

injectValue :: (forall a. f a -> g a) -> Value f -> Value g
injectValue f (Value ty x) = Value ty (f x)
