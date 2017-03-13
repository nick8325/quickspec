-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, CPP, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, ExistentialQuantification, PolyKinds, TypeFamilies, FlexibleContexts, StandaloneDeriving #-}
-- To avoid a warning about TyVarNumber's constructor being unused:
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module QuickSpec.Type(
  -- Types.
  Typeable,
  Type, TyCon(..), tyCon, toTyCon, fromTyCon, A, B, C, D, E,
  typeOf, typeRep, applyType, toTypeRep, fromTypeRep,
  arrowType, typeArgs, typeRes, typeDrop, typeArity, oneTypeVar, skolemiseTypeVars,
  isDictionary, getDictionary,
  -- Things that have types.
  Typed(..), typeSubst, typesDL, tyVars, cast,
  TypeView(..),
  Apply(..), apply, canApply,
  -- Polymorphic types.
  canonicaliseType,
  Poly, poly, unPoly, polyTyp, polyMap, polyApply, polyPair, polyList, polyMgu,
  -- Dynamic values.
  Value, toValue, fromValue,
  Unwrapped(..), unwrap, Wrapper(..),
  mapValue, forValue, ofValue, withValue, pairValues, wrapFunctor, unwrapFunctor) where

#include "errors.h"
import Control.Applicative
import Control.Monad
import Data.DList(DList)
import Data.Maybe
import qualified Data.Typeable as Ty
import Data.Typeable(Typeable)
import qualified Data.Typeable.Internal as Ty
import GHC.Exts(Any)
import GHC.Stack
import Test.QuickCheck
import Unsafe.Coerce
import Data.Constraint
import Twee.Base
import qualified Twee.Term as Term
import qualified Twee.Label as Label
import Data.Ord

deriving instance Typeable (() :: Constraint)

-- A (possibly polymorphic) type.
type Type = Term TyCon

data TyCon = Arrow | TyCon Ty.TyCon deriving (Eq, Ord, Show)

instance Label.Labelled Ty.TyCon where
  cache = tyConCache

{-# NOINLINE tyConCache #-}
tyConCache :: Label.Cache Ty.TyCon
tyConCache = Label.mkCache

instance Numbered TyCon where
  toInt Arrow = 0
  toInt (TyCon ty) = Label.label ty + 1

  fromInt 0 = Arrow
  fromInt n = TyCon (fromMaybe __ (Label.find (n-1)))

instance Pretty TyCon where
  pPrint Arrow = text "->"
  pPrint (TyCon x) = text (show x)
instance PrettyTerm TyCon where
  termStyle Arrow =
    fixedArity 2 $
    TermStyle $ \l p d [x, y] ->
      pPrintParen (p > 8) $
        pPrintPrec l 9 x <+> d <+>
        pPrintPrec l 0 y

  termStyle (TyCon con)
    | con == listTyCon =
      fixedArity 1 $
      TermStyle $ \l _ _ [x] -> brackets (pPrintPrec l 0 x)
    | take 2 (show con) == "(," ||
      take 3 (show con) == "(%," =
      fixedArity (1+length (filter (== ',') (show con))) tupleStyle
  termStyle _ = curried

-- Type variables.
type A = TyVarNumber Zero
type B = TyVarNumber (Succ Zero)
type C = TyVarNumber (Succ (Succ Zero))
type D = TyVarNumber (Succ (Succ (Succ Zero)))
type E = TyVarNumber (Succ (Succ (Succ (Succ Zero))))
newtype TyVarNumber a = TyVarNumber Any deriving Typeable
data Zero deriving Typeable
data Succ a deriving Typeable

typeOf :: Typeable a => a -> Type
typeOf x = fromTypeRep (Ty.typeOf x)

typeRep :: Typeable (a :: k) => proxy a -> Type
typeRep x = fromTypeRep (Ty.typeRep x)

applyType :: Type -> Type -> Type
applyType (Fun f tys) ty = build (fun f (fromTermList tys ++ [ty]))
applyType _ _ = ERROR("tried to apply type variable")

arrowType :: [Type] -> Type -> Type
arrowType [] res = res
arrowType (arg:args) res = app Arrow [arg, arrowType args res]

typeArgs :: Type -> [Type]
typeArgs (App Arrow [arg, res]) = arg:typeArgs res
typeArgs _ = []

typeRes :: Type -> Type
typeRes (App Arrow [_, res]) = typeRes res
typeRes ty = ty

typeDrop :: Int -> Type -> Type
typeDrop 0 ty = ty
typeDrop n (App Arrow [_, ty]) = typeDrop (n-1) ty

typeArity :: Type -> Int
typeArity = length . typeArgs

oneTypeVar :: Typed a => a -> a
oneTypeVar = typeSubst (const (var (MkVar 0)))

skolemiseTypeVars :: Typed a => a -> a
skolemiseTypeVars = typeSubst (const aTy)
  where
    aTy = app (fromTyCon (mkCon (__ :: A))) []

fromTypeRep :: Ty.TypeRep -> Type
fromTypeRep ty =
  case Ty.splitTyConApp ty of
    (tyVar, [ty]) | tyVar == varTyCon -> build (var (MkVar (fromTyVar ty)))
    (tyCon, tys) -> app (fromTyCon tyCon) (map fromTypeRep tys)
  where
    fromTyVar ty =
      case Ty.splitTyConApp ty of
        (tyCon, [ty']) | tyCon == succTyCon -> succ (fromTyVar ty')
        (tyCon, []) | tyCon == zeroTyCon -> 0

fromTyCon :: Ty.TyCon -> TyCon
fromTyCon ty
  | ty == arrowTyCon = Arrow
  | otherwise = TyCon ty

arrowTyCon, commaTyCon, listTyCon, varTyCon, succTyCon, zeroTyCon, dictTyCon :: Ty.TyCon
arrowTyCon = mkCon (__ :: () -> ())
commaTyCon = mkCon (__ :: ((),()))
listTyCon  = mkCon (__ :: [()])
varTyCon   = mkCon (__ :: TyVarNumber ())
succTyCon  = mkCon (__ :: Succ ())
zeroTyCon  = mkCon (__ :: Zero)
dictTyCon  = mkCon (__ :: Dict ())

mkCon :: Typeable a => a -> Ty.TyCon
mkCon = fst . Ty.splitTyConApp . Ty.typeOf

tyCon :: Typeable a => a -> TyCon
tyCon = fromTyCon . mkCon

-- For showing types.
toTypeRep :: Type -> Ty.TypeRep
toTypeRep (App tyCon tys) = Ty.mkTyConApp (toTyCon tyCon) (map toTypeRep tys)
toTypeRep (Var (MkVar n)) = Ty.mkTyConApp varTyCon [toTyVar n]
  where
    toTyVar 0 = Ty.mkTyConApp zeroTyCon []
    toTyVar n = Ty.mkTyConApp succTyCon [toTyVar (n-1)]

toTyCon :: TyCon -> Ty.TyCon
toTyCon Arrow = arrowTyCon
toTyCon (TyCon tyCon) = tyCon

getDictionary :: Type -> Maybe Type
getDictionary (App (TyCon tc) [ty]) | tc == dictTyCon = Just ty
getDictionary _ = Nothing

isDictionary :: Type -> Bool
isDictionary = isJust . getDictionary

-- CoArbitrary instances.
instance CoArbitrary Ty.TypeRep where
#if __GLASGOW_HASKELL__ >= 710
  coarbitrary (Ty.TypeRep (Ty.Fingerprint x y) _ _ _) =
    coarbitrary x . coarbitrary y
#else
  coarbitrary (Ty.TypeRep (Ty.Fingerprint x y) _ _) =
    coarbitrary x . coarbitrary y
#endif

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
  typeReplace :: (TermListOf Type -> Builder TyCon) -> a -> a

{-# INLINE typeSubst #-}
typeSubst :: (Typed a, Substitution TyCon s) => s -> a -> a
typeSubst s x = typeReplace (Term.substList s) x

-- Using the normal term machinery on types.
newtype TypeView a = TypeView { unTypeView :: a }
instance Typed a => Symbolic (TypeView a) where
  type ConstantOf (TypeView a) = TyCon
  term = typ . unTypeView
  termsDL = fmap singleton . typesDL . unTypeView
  replace f = TypeView . typeReplace f . unTypeView

typesDL :: Typed a => a -> DList Type
typesDL ty = return (typ ty) `mplus` otherTypesDL ty

tyVars :: Typed a => a -> [Var]
tyVars = vars . TypeView

cast :: Typed a => Type -> a -> Maybe a
cast ty x = do
  s <- match (typ x) ty
  return (typeSubst s x)

-- Typed things that support function application.
class Typed a => Apply a where
  -- Apply a function to its argument.
  tryApply :: a -> a -> Maybe a

infixl `apply`
apply :: (HasCallStack, Apply a) => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing -> ERROR("apply: ill-typed term: (" ++ prettyShow (typ f) ++ ") to  (" ++ prettyShow (typ x) ++ ")")
    Just y -> y

canApply :: Apply a => a -> a -> Bool
canApply f x = isJust (tryApply f x)

-- Instances.
instance Typed Type where
  typ = id
  typeReplace = replace

instance Apply Type where
  tryApply (App Arrow [arg, res]) t | t == arg = Just res
  tryApply _ _ = Nothing

instance (Typed a, Typed b) => Typed (a, b) where
  typ (x, y) = app (TyCon commaTyCon) [typ x, typ y]
  otherTypesDL (x, y) = otherTypesDL x `mplus` otherTypesDL y
  typeReplace f (x, y) = (typeReplace f x, typeReplace f y)

instance Typed a => Typed [a] where
  typ [] = typeOf ()
  typ (x:xs) = typ (x, xs)
  otherTypesDL = msum . map otherTypesDL
  typeReplace f xs = map (typeReplace f) xs

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

polyMap :: (Typed a, Typed b) => (a -> b) -> Poly a -> Poly b
polyMap f (Poly x) = poly (f x)

polyApply :: (Typed a, Typed b, Typed c) => (a -> b -> c) -> Poly a -> Poly b -> Poly c
polyApply f (Poly x) (Poly y) = poly (f x y')
  where
    y' = typeSubst (\(MkVar n) -> var (MkVar (k+n))) y
    k  = maximum (fmap bound (typesDL x))

polyPair :: (Typed a, Typed b) => Poly a -> Poly b -> Poly (a, b)
polyPair = polyApply (,)

polyList :: Typed a => [Poly a] -> Poly [a]
polyList [] = poly []
polyList (x:xs) = polyApply (:) x (polyList xs)

polyMgu :: Poly Type -> Poly Type -> Maybe (Poly Type)
polyMgu ty1 ty2 = do
  let (ty1', ty2') = unPoly (polyPair ty1 ty2)
  sub <- unify ty1' ty2'
  return (poly (typeSubst sub ty1'))

instance Typed a => Typed (Poly a) where
  typ = typ . unPoly
  otherTypesDL = otherTypesDL . unPoly
  typeReplace f (Poly x) = poly (typeReplace f x)

instance Apply a => Apply (Poly a) where
  tryApply f x = do
    let (f', (x', resType)) = unPoly (polyPair f (polyPair x (poly (build (var (MkVar 0))))))
    s <- unify (typ f') (arrowType [typ x'] resType)
    let (f'', x'') = typeSubst s (f', x')
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
toValue x = Value (typeOf (__ :: a)) (toAny x)

fromValue :: forall f (a :: *). Typeable a => Value f -> Maybe (f a)
fromValue x = do
  guard (typ x == typeOf (__ :: a))
  return (fromAny (value x))

instance Typed (Value f) where
  typ = valueType
  typeReplace f (Value ty x) = Value (typeReplace f ty) x
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
        else ERROR("non-matching types"))

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
    ty = typeRep (__ :: proxy g) `applyType` typ x `applyType` typ y

wrapFunctor :: forall f g h. Typeable h => (forall a. f a -> g (h a)) -> Value f -> Value g
wrapFunctor f x =
  ty `seq`
  Value {
    valueType = ty,
    value = toAny (f (value x)) }
  where
    ty = typeRep (__ :: proxy h) `applyType` valueType x

unwrapFunctor :: forall f g h. Typeable g => (forall a. f (g a) -> h a) -> Value f -> Value h
unwrapFunctor f x =
  case typ x of
    App _ tys@(_:_) ->
      case ty `applyType` last tys == typ x of
        True ->
          Value {
            valueType = last tys,
            value = f (fromAny (value x)) }
        False ->
          ERROR("non-matching types")
  where
    ty = typeRep (__ :: proxy g)
