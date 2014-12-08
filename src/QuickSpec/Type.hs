-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, ExistentialQuantification, PolyKinds, TypeFamilies #-}
-- To avoid a warning about TyVarNumber's constructor being unused:
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module QuickSpec.Type(
  -- Types.
  Typeable,
  Type, TyCon(..), tyCon, toTyCon, fromTyCon, TyVar(..), A, B, C, D,
  typeOf, typeRep, applyType, toTypeRep, fromTypeRep,
  arrowType, typeArgs, typeRes, arity, oneTypeVar, skolemiseTypeVars,
  -- Things that have types.
  Typed(..), typesDL, tyVars, cast,
  TypeView(..),
  Apply(..), apply, canApply,
  -- Polymorphic types.
  Poly, poly, unPoly, polyTyp, polyPair, polyMgu,
  -- Dynamic values.
  Value, toValue, fromValue,
  Unwrapped(..), unwrap, Wrapper(..),
  mapValue, forValue, ofValue, withValue, pairValues, unwrapFunctor) where

#include "errors.h"
import Control.Applicative
import Control.Monad
import Data.DList(DList)
import Data.Maybe
import qualified Data.Typeable as Ty
import Data.Typeable(Typeable)
import qualified Data.Typeable.Internal as Ty
import GHC.Exts(Any)
import QuickSpec.Base
import Test.QuickCheck
import Unsafe.Coerce

-- A (possibly polymorphic) type.
type Type = Tm TyCon TyVar

data TyCon = Arrow | TyCon Ty.TyCon deriving (Eq, Ord, Show)
newtype TyVar = TyVar { tyVarNumber :: Int } deriving (Eq, Ord, Show, Enum, Numbered)

instance Pretty TyCon where
  pretty Arrow = text "->"
  pretty (TyCon x) = text (show x)
instance PrettyTerm TyCon where
  termStyle Arrow = Infixr 8
  termStyle (TyCon con)
    | con == listTyCon = ListType
    | take 2 (show con) == "(," = TupleType
  termStyle _ = Curried
instance Pretty TyVar where
  pretty (TyVar n) = text (supply [[c] | c <- ['a'..'z']] !! n)

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

typeRep :: Typeable (a :: k) => proxy a -> Type
typeRep x = fromTypeRep (Ty.typeRep x)

applyType :: Type -> Type -> Type
applyType (Fun f tys) ty = Fun f (tys ++ [ty])
applyType _ _ = ERROR "tried to apply type variable"

arrowType :: [Type] -> Type -> Type
arrowType [] res = res
arrowType (arg:args) res = Fun Arrow [arg, arrowType args res]

typeArgs :: Type -> [Type]
typeArgs (Fun Arrow [arg, res]) = arg:typeArgs res
typeArgs _ = []

typeRes :: Type -> Type
typeRes (Fun Arrow [_, res]) = typeRes res
typeRes ty = ty

arity :: Type -> Int
arity = length . typeArgs

oneTypeVar :: Typed a => a -> a
oneTypeVar = typeSubst (const (Var (TyVar 0)))

skolemiseTypeVars :: Typed a => a -> a
skolemiseTypeVars = typeSubst (const aTy)
  where
    aTy = Fun (fromTyCon (con (undefined :: A))) []

fromTypeRep :: Ty.TypeRep -> Type
fromTypeRep ty =
  case Ty.splitTyConApp ty of
    (tyVar, [ty]) | tyVar == varTyCon -> Var (TyVar (fromTyVar ty))
    (tyCon, tys) -> Fun (fromTyCon tyCon) (map fromTypeRep tys)
  where
    fromTyVar ty =
      case Ty.splitTyConApp ty of
        (tyCon, [ty']) | tyCon == succTyCon -> succ (fromTyVar ty')
        (tyCon, []) | tyCon == zeroTyCon -> 0

fromTyCon :: Ty.TyCon -> TyCon
fromTyCon tyCon
  | tyCon == arrowTyCon = Arrow
  | otherwise = TyCon tyCon

arrowTyCon, commaTyCon, listTyCon, varTyCon, succTyCon, zeroTyCon :: Ty.TyCon
arrowTyCon = con (undefined :: () -> ())
commaTyCon = con (undefined :: ((),()))
listTyCon  = con (undefined :: [()])
varTyCon   = con (undefined :: TyVarNumber ())
succTyCon  = con (undefined :: Succ ())
zeroTyCon  = con (undefined :: Zero)

con :: Typeable a => a -> Ty.TyCon
con = fst . Ty.splitTyConApp . Ty.typeOf

tyCon :: Typeable a => a -> TyCon
tyCon = fromTyCon . con

-- For showing types.
toTypeRep :: Type -> Ty.TypeRep
toTypeRep (Fun tyCon tys) = Ty.mkTyConApp (toTyCon tyCon) (map toTypeRep tys)
toTypeRep (Var (TyVar n)) = Ty.mkTyConApp varTyCon [toTyVar n]
  where
    toTyVar 0 = Ty.mkTyConApp zeroTyCon []
    toTyVar n = Ty.mkTyConApp succTyCon [toTyVar (n-1)]

toTyCon :: TyCon -> Ty.TyCon
toTyCon Arrow = arrowTyCon
toTyCon (TyCon tyCon) = tyCon

-- CoArbitrary instances.
instance CoArbitrary Ty.TypeRep where
  coarbitrary (Ty.TypeRep (Ty.Fingerprint x y) _ _) =
    coarbitrary x . coarbitrary y

instance CoArbitrary Type where
  coarbitrary = coarbitrary . toTypeRep

-- Things with types.
class Typed a where
  -- The type.
  typ :: a -> Type
  -- Any other types that may appear in subterms etc
  -- (enough at least to collect all type variables and type constructors).
  otherTypesDL :: a -> DList Type
  otherTypesDL _ = mzero
  -- Substitute for all type variables.
  typeSubst :: (TyVar -> Type) -> a -> a

-- Using the normal term machinery on types.
newtype TypeView a = TypeView { unTypeView :: a }
instance Typed a => Symbolic (TypeView a) where
  type ConstantOf (TypeView a) = TyCon
  type VariableOf (TypeView a) = TyVar
  termsDL = typesDL . unTypeView
  substf sub = TypeView . typeSubst sub . unTypeView

typesDL :: Typed a => a -> DList Type
typesDL ty = return (typ ty) `mplus` otherTypesDL ty

tyVars :: Typed a => a -> [TyVar]
tyVars = vars . TypeView

cast :: Typed a => Type -> a -> Maybe a
cast ty x = do
  s <- match (typ x) ty
  return (typeSubst (evalSubst s) x)

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
  typeSubst = substf

instance Apply Type where
  tryApply (Fun Arrow [arg, res]) t | t == arg = Just res
  tryApply _ _ = Nothing

instance (Typed a, Typed b) => Typed (a, b) where
  typ (x, y) = Fun (TyCon commaTyCon) [typ x, typ y]
  otherTypesDL (x, y) = otherTypesDL x `mplus` otherTypesDL y
  typeSubst f (x, y) = (typeSubst f x, typeSubst f y)

-- Represents a forall-quantifier over all the type variables in a type.
-- Wrapping a term in Poly normalises the type by alpha-renaming
-- type variables canonically.
newtype Poly a = Poly { unPoly :: a }
  deriving (Eq, Ord, Show, Pretty, Typeable)

poly :: Typed a => a -> Poly a
poly x = Poly (canonicaliseType x)

canonicaliseType :: Typed a => a -> a
canonicaliseType = unTypeView . canonicalise . TypeView

polyTyp :: Typed a => Poly a -> Poly Type
polyTyp (Poly x) = Poly (typ x)

polyPair :: (Typed a, Typed b) => Poly a -> Poly b -> Poly (a, b)
polyPair (Poly x) (Poly y) = poly (x, y')
  where
    y' = typeSubst (\(TyVar n) -> Var (TyVar (-n-1))) y

polyMgu :: Poly Type -> Poly Type -> Maybe (Poly Type)
polyMgu ty1 ty2 = do
  let (ty1', ty2') = unPoly (polyPair ty1 ty2)
  sub <- unify ty1' ty2'
  return (poly (typeSubst (evalSubst sub) ty1'))

instance Typed a => Typed (Poly a) where
  typ = typ . unPoly
  otherTypesDL = otherTypesDL . unPoly
  typeSubst f (Poly x) = poly (typeSubst f x)

instance Apply a => Apply (Poly a) where
  tryApply f x = do
    let (f', (x', resType)) = unPoly (polyPair f (polyPair x (poly (Var (TyVar 0)))))
    s <- unify (typ f') (arrowType [typ x'] resType)
    let (f'', x'') = typeSubst (evalSubst s) (f', x')
    fmap poly (tryApply f'' x'')

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

toValue :: forall f (a :: *). Typeable a => f a -> Value f
toValue x = Value (typeOf (undefined :: a)) (toAny x)

fromValue :: forall f (a :: *). Typeable a => Value f -> Maybe (f a)
fromValue x = do
  guard (typ x == typeOf (undefined :: a))
  return (fromAny (value x))

instance Typed (Value f) where
  typ = valueType
  typeSubst f (Value ty x) = Value (typeSubst f ty) x
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

withValue :: Value f -> (forall a. f a -> b) -> b
withValue x f = ofValue f x

pairValues :: forall f g. Typeable g => (forall a b. f a -> f b -> f (g a b)) -> Value f -> Value f -> Value f
pairValues f x y =
  ty `seq`
  Value {
    valueType = ty,
    value = toAny (f (value x) (value y)) }
  where
    ty = typeRep (undefined :: proxy g) `applyType` typ x `applyType` typ y

unwrapFunctor :: forall f g h. Typeable g => (forall a. f (g a) -> h a) -> Value f -> Value h
unwrapFunctor f x =
  case typ x of
    Fun _ tys@(_:_) ->
      case ty `applyType` last tys == typ x of
        True ->
          Value {
            valueType = last tys,
            value = f (fromAny (value x)) }
        False ->
          ERROR "non-matching types"
  where
    ty = typeRep (undefined :: proxy g)
