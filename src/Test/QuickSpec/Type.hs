-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, ExistentialQuantification #-}
-- To avoid a warning about TyVarNumber's constructor being unused:
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module Test.QuickSpec.Type(
  -- Types.
  Typeable,
  Type, TyCon(..), TyVar(..), A, B, C, D,
  typeOf, arrowType, arity, toTypeRep, fromTypeRep,
  -- Things that have types.
  Typed(..), typeSubst, tyVars,
  Apply(..), apply, canApply,
  -- Polymorphic types.
  Poly, poly, unPoly, polyTyp,
  -- Dynamic values.
  Value, toValue, fromValue,
  Unwrapped(..), unwrap, Wrapper(..),
  mapValue, forValue, ofValue, pairValues) where

#include "errors.h"

import Test.QuickSpec.Base
import Test.QuickSpec.Utils
import Data.Typeable(Typeable)
import qualified Data.Typeable as Ty
import GHC.Exts(Any)
import Unsafe.Coerce
import Control.Applicative
import Data.Maybe
import qualified Data.DList as DList
import Data.Functor.Identity
import Data.Traversable(traverse)
import qualified Data.Map as Map
import qualified Data.Rewriting.Substitution.Type as T
import Data.List
import Control.Monad
import Control.Monad.Trans.Writer

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

arrowTyCon, commaTyCon, varTyCon, succTyCon, zeroTyCon :: Ty.TyCon
arrowTyCon = con (undefined :: () -> ())
commaTyCon = con (undefined :: ((),()))
varTyCon   = con (undefined :: TyVarNumber ())
succTyCon  = con (undefined :: Succ ())
zeroTyCon  = con (undefined :: Zero)

con :: Typeable a => a -> Ty.TyCon
con = fst . Ty.splitTyConApp . Ty.typeOf

-- For showing types.
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

typeSubst :: Typed a => (TyVar -> Type) -> a -> a
typeSubst f t = runIdentity (typeSubstA (return . f) t)

tyVars :: Typed a => a -> [TyVar]
tyVars t = DList.toList (execWriter (typeSubstA f t))
  where
    f x = do
      tell (DList.singleton x)
      return (Var x)

-- Typed things that support function application.
class Typed a => Apply a where
  -- Apply a function to its argument.
  tryApply :: a -> a -> Maybe a

infixl `apply`
apply :: Apply a => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing -> ERROR "apply: ill-typed term"
    Just y -> y

canApply :: Apply a => a -> a -> Bool
canApply f x = isJust (tryApply f x)

-- Instances.
instance Typed Type where
  typ = id
  typeSubstA s (Var x) = s x
  typeSubstA s (Fun f xs) =
    Fun f <$> traverse (typeSubstA s) xs

instance Apply Type where
  tryApply (Fun Arrow [arg, res]) t | t == arg = Just res
  tryApply _ _ = Nothing

instance (Typed a, Typed b) => Typed (a, b) where
  typ (x, y) = Fun (TyCon commaTyCon) [typ x, typ y]
  typeSubstA f (x, y) = liftA2 (,) (typeSubstA f x) (typeSubstA f y)

-- Represents a forall-quantifier over all the type variables in a type.
-- Wrapping a term in Poly normalises the type by alpha-renaming
-- type variables canonically.
newtype Poly a = Poly { unPoly :: a }
  deriving (Eq, Ord, Show, Pretty, Typeable)

poly :: Typed a => a -> Poly a
poly x = Poly (normaliseType x)

normaliseType :: Typed a => a -> a
normaliseType t = typeSubst (evalSubst s) t
  where
    s = T.fromMap (Map.fromList (zip tvs (map (Var . TyVar) [0..])))
    tvs = tvs' ++ (usort (tyVars t) \\ tvs')
    tvs' = usort (tyVars (typ t))

polyTyp :: Typed a => Poly a -> Poly Type
polyTyp (Poly x) = Poly (typ x)

instance Typed a => Typed (Poly a) where
  typ = typ . unPoly
  typeSubstA f (Poly x) = fmap poly (typeSubstA f x)

instance Apply a => Apply (Poly a) where
  tryApply (Poly f) (Poly x) = do
    -- Rename x's type variables to not clash with f's.
    let x' = typeSubst (\(TyVar n) -> Var (TyVar (-n-1))) x
        resType = Var (TyVar 0)
    s <- unify (typ f) (arrowType [typ x'] resType)
    let (f', x'') = typeSubst (evalSubst s) (f, x')
    fmap poly (tryApply f' x'')

-- Dynamic values inside an applicative functor.
data Value f =
  Value {
    valueType :: Type,
    value :: f Any }

instance Show (Value f) where
  show x = "<<" ++ prettyShow (typ x) ++ ">>"

fromAny :: f Any -> f a
fromAny = unsafeCoerce

toAny :: f a -> f Any
toAny = unsafeCoerce

toValue :: forall f a. Typeable a => f a -> Value f
toValue x = Value (typeOf (undefined :: a)) (toAny x)

fromValue :: forall f a. Typeable a => Value f -> Maybe (f a)
fromValue x = do
  guard (typ x == typeOf (undefined :: a))
  return (fromAny (value x))

instance Typed (Value f) where
  typ = valueType
  typeSubstA f (Value ty x) = Value <$> typeSubstA f ty <*> pure x
instance Applicative f => Apply (Value f) where
  tryApply f x = do
    ty <- tryApply (typ f) (typ x)
    return (Value ty (fromAny (value f) <*> value x))

-- Unwrap a value to get at the thing inside, while still being able
-- to wrap it up again.
data Unwrapped f = forall a. f a `In` Wrapper a
data Wrapper a =
  Wrapper {
    wrap :: forall g. g a -> Value g,
    reunwrap :: forall g. Value g -> g a }

unwrap :: Value f -> Unwrapped f
unwrap x =
  value x `In`
    Wrapper
      (\y -> Value (typ x) y)
      (\y ->
        if typ x == typ y
        then fromAny (value y)
        else ERROR "non-matching types")

mapValue :: (forall a. f a -> g a) -> Value f -> Value g
mapValue f v =
  case unwrap v of
    x `In` w -> wrap w (f x)

forValue :: Value f -> (forall a. f a -> g a) -> Value g
forValue x f = mapValue f x

ofValue :: (forall a. f a -> b) -> Value f -> b
ofValue f v =
  case unwrap v of
    x `In` _ -> f x

pairValues :: (forall a. f a -> g a -> h a) -> Value f -> Value g -> Value h
pairValues f x y =
  case unwrap x of
    x `In` w ->
      wrap w (f x (reunwrap w y))
