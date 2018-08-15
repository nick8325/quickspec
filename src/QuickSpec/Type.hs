-- | This module is internal to QuickSpec.
--
-- Polymorphic types and dynamic values.
{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, ExistentialQuantification, PolyKinds, TypeFamilies, FlexibleContexts, StandaloneDeriving, PatternGuards, MultiParamTypeClasses, ConstraintKinds, DataKinds, GADTs #-}
-- To avoid a warning about TyVarNumber's constructor being unused:
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module QuickSpec.Type(
  -- * Types
  Typeable,
  Type, TyCon(..), tyCon, fromTyCon, A, B, C, D, E, ClassA, ClassB, ClassC, ClassD, ClassE, ClassF, SymA, typeVar, isTypeVar,
  typeOf, typeRep, typeFromTyCon, applyType, fromTypeRep,
  arrowType, isArrowType, unpackArrow, typeArgs, typeRes, typeDrop, typeArity,
  isDictionary, getDictionary, splitConstrainedType, dictArity, pPrintType,
  -- * Things that have types
  Typed(..), typeSubst, typesDL, tyVars, cast, matchType,
  TypeView(..),
  Apply(..), apply, canApply,
  oneTypeVar, defaultTo, skolemiseTypeVars,
  -- * Polymorphic types
  canonicaliseType,
  Poly, toPolyValue, poly, unPoly, polyTyp, polyRename, polyApply, polyPair, polyList, polyMgu,
  -- * Dynamic values
  Value, toValue, fromValue, valueType,
  unwrap, Unwrapped(..), Wrapper(..),
  mapValue, forValue, ofValue, withValue, pairValues, wrapFunctor, unwrapFunctor, bringFunctor) where

import Control.Monad
import Data.DList(DList)
import Data.Maybe
import qualified Data.Typeable as Ty
import Data.Typeable(Typeable)
import GHC.Exts(Any)
import Test.QuickCheck
import Unsafe.Coerce
import Data.Constraint
import Twee.Base
import Data.Proxy
import Data.List
import Data.Char
import Data.Functor.Identity

-- | A (possibly polymorphic) type.
type Type = Term TyCon

-- | A type constructor.
data TyCon =
    -- | The function type constructor @(->)@.
    Arrow
    -- | An ordinary Haskell type constructor.
  | TyCon Ty.TyCon
    -- | A string. Can be used to represent miscellaneous types that do not
    -- really exist in Haskell.
  | String String
  deriving (Eq, Ord, Show)

instance Pretty TyCon where
  pPrint Arrow = text "->"
  pPrint (String x) = text x
  pPrint (TyCon x) = text (show x)
instance PrettyTerm TyCon where
  termStyle Arrow =
    fixedArity 2 $
    TermStyle $ \l p d [x, y] ->
      maybeParens (p > 8) $
        pPrintPrec l 9 x <+> d <+>
        pPrintPrec l 0 y

  termStyle (String _) = curried

  termStyle (TyCon con)
    | con == listTyCon =
      fixedArity 1 $
      TermStyle $ \l _ _ [x] -> brackets (pPrintPrec l 0 x)
    | show con == "()" || show con == "(%%)" =
      fixedArity 0 tupleStyle -- by analogy with case below
    | take 2 (show con) == "(," ||
      take 3 (show con) == "(%," =
      fixedArity (1+length (filter (== ',') (show con))) tupleStyle
    | isAlphaNum (head (show con)) = curried
    | otherwise = infixStyle 5

-- Type and class variables.
newtype A = A Any deriving Typeable
newtype B = B Any deriving Typeable
newtype C = C Any deriving Typeable
newtype D = D Any deriving Typeable
newtype E = E Any deriving Typeable

class ClassA
deriving instance Typeable ClassA
class ClassB
deriving instance Typeable ClassB
class ClassC
deriving instance Typeable ClassC
class ClassD
deriving instance Typeable ClassD
class ClassE
deriving instance Typeable ClassE
class ClassF
deriving instance Typeable ClassF

-- | A polymorphic type of kind Symbol.
type SymA = "__polymorphic_symbol__"

-- | All type variables that are defined in this module.
typeVars :: [Ty.TypeRep]
typeVars =
  [Ty.typeRep (Proxy :: Proxy A),
   Ty.typeRep (Proxy :: Proxy B),
   Ty.typeRep (Proxy :: Proxy C),
   Ty.typeRep (Proxy :: Proxy D),
   Ty.typeRep (Proxy :: Proxy E),
   Ty.typeRep (Proxy :: Proxy ClassA),
   Ty.typeRep (Proxy :: Proxy ClassB),
   Ty.typeRep (Proxy :: Proxy ClassC),
   Ty.typeRep (Proxy :: Proxy ClassD),
   Ty.typeRep (Proxy :: Proxy ClassE),
   Ty.typeRep (Proxy :: Proxy ClassF),
   Ty.typeRep (Proxy :: Proxy SymA)]

-- | A type variable.
typeVar :: Type
typeVar = typeRep (Proxy :: Proxy A)

-- | Check if a type is a type variable.
isTypeVar :: Type -> Bool
isTypeVar = isVar

-- | Construct a type from a `Typeable`.
typeOf :: Typeable a => a -> Type
typeOf x = fromTypeRep (Ty.typeOf x)

-- | Construct a type from a `Typeable`.
typeRep :: Typeable (a :: k) => proxy a -> Type
typeRep x = fromTypeRep (Ty.typeRep x)

-- | Turn a `TyCon` into a type.
typeFromTyCon :: TyCon -> Type
typeFromTyCon tc = build (con (fun tc))

-- | Function application for type constructors.
--
-- For example, @applyType (typeRep (Proxy :: Proxy [])) (typeRep (Proxy :: Proxy Int)) == typeRep (Proxy :: Proxy [Int])@.
applyType :: Type -> Type -> Type
applyType (App f tys) ty = build (app f (unpack tys ++ [ty]))
applyType _ _ = error "tried to apply type variable"

-- | Construct a function type.
arrowType :: [Type] -> Type -> Type
arrowType [] res = res
arrowType (arg:args) res =
  build (app (fun Arrow) [arg, arrowType args res])

-- | Is a given type a function type?
isArrowType :: Type -> Bool
isArrowType = isJust . unpackArrow

-- | Decompose a function type into (argument, result).
--
-- For multiple-argument functions, unpacks one argument.
unpackArrow :: Type -> Maybe (Type, Type)
unpackArrow (App (F Arrow) (Cons t (Cons u Empty))) =
  Just (t, u)
unpackArrow _ =
  Nothing

-- | The arguments of a function type.
typeArgs :: Type -> [Type]
typeArgs (App (F Arrow) (Cons arg (Cons res Empty))) =
  arg:typeArgs res
typeArgs _ = []

-- | The result of a function type.
typeRes :: Type -> Type
typeRes (App (F Arrow) (Cons _ (Cons res Empty))) =
  typeRes res
typeRes ty = ty

-- | Given the type of a function, returns the type of applying that function to
-- @n@ arguments. Crashes if the type does not have enough arguments.
typeDrop :: Int -> Type -> Type
typeDrop 0 ty = ty
typeDrop n (App (F Arrow) (Cons _ (Cons ty Empty))) =
  typeDrop (n-1) ty
typeDrop _ _ =
  error "typeDrop on non-function type"

-- | How many arguments does a function take?
typeArity :: Type -> Int
typeArity = length . typeArgs

-- | Unify all type variables in a type.
oneTypeVar :: Typed a => a -> a
oneTypeVar = typeSubst (const (var (V 0)))

-- | Replace all type variables with a particular type.
defaultTo :: Typed a => Type -> a -> a
defaultTo def = typeSubst (const def)

-- | Make a type ground by replacing all type variables
-- with Skolem constants.
skolemiseTypeVars :: Typed a => a -> a
skolemiseTypeVars = typeSubst (const aTy)
  where
    aTy = build (con (fun (tyCon (Proxy :: Proxy A))))

-- | Construct a type from a `Ty.TypeRep`.
fromTypeRep :: Ty.TypeRep -> Type
fromTypeRep ty
  | Just n <- elemIndex ty typeVars =
      build (var (V n))
  | otherwise =
    let (tyCon, tys) = Ty.splitTyConApp ty in
    build (app (fun (fromTyCon tyCon)) (map fromTypeRep tys))

-- | Construct a `TyCon` type from a "Data.Typeable" `Ty.TyCon`.
fromTyCon :: Ty.TyCon -> TyCon
fromTyCon ty
  | ty == arrowTyCon = Arrow
  | otherwise = TyCon ty

-- | Some built-in type consructors.
arrowTyCon, commaTyCon, listTyCon, dictTyCon :: Ty.TyCon
arrowTyCon = mkCon (Proxy :: Proxy (->))
commaTyCon = mkCon (Proxy :: Proxy (,))
listTyCon  = mkCon (Proxy :: Proxy [])
dictTyCon  = mkCon (Proxy :: Proxy Dict)

mkCon :: Typeable a => proxy a -> Ty.TyCon
mkCon = fst . Ty.splitTyConApp . Ty.typeRep

-- | Get the outermost `TyCon` of a `Typeable`.
tyCon :: Typeable a => proxy a -> TyCon
tyCon = fromTyCon . mkCon

-- | Check if a type is of the form @`Dict` c@, and if so, return @c@.
getDictionary :: Type -> Maybe Type
getDictionary (App (F (TyCon dict)) (Cons ty Empty))
  | dict == dictTyCon = Just ty
getDictionary _ = Nothing

-- | Check if a type is of the form @`Dict` c@.
isDictionary :: Type -> Bool
isDictionary = isJust . getDictionary

-- | Count how many dictionary arguments a type has.
dictArity :: Type -> Int
dictArity = length . takeWhile isDictionary . typeArgs

-- | Split a type into constraints and normal type.
splitConstrainedType :: Type -> ([Type], Type)
splitConstrainedType ty =
  (dicts, arrowType rest (typeRes ty))
  where
    (dicts, rest) = splitAt (dictArity ty) (typeArgs ty)

-- CoArbitrary instances.
instance CoArbitrary Type where
  coarbitrary = coarbitrary . singleton
instance CoArbitrary (TermList TyCon) where
  coarbitrary Empty = variant 0
  coarbitrary (ConsSym (Var (V x)) ts) =
    variant 1 . coarbitrary x . coarbitrary ts
  coarbitrary (ConsSym (App f _) ts) =
    variant 2 . coarbitrary (fun_id f) . coarbitrary ts

-- | Pretty-print a type. Differs from the `Pretty` instance by printing type
-- variables in lowercase.
pPrintType :: Type -> Doc
pPrintType = ppr . typeSubst (\(V x) -> build (con (fun (String (as !! x))))) . canonicalise
  where
    as = supply [[x] | x <- ['a'..'z']]
    -- Print dictionary arguments specially
    ppr ty
      | Just (dict, res) <- unpackArrow ty,
        Just constraint <- getDictionary dict =
      pPrint constraint <+> text "=>" <+> ppr res
    ppr ty = pPrint ty

-- | A class for things that have a type.
class Typed a where
  -- | The type.
  typ :: a -> Type
  -- | Types that appear elsewhere in the `Typed`, for example, types of subterms.
  -- Should return everything which is affected by `typeSubst`.
  otherTypesDL :: a -> DList Type
  otherTypesDL _ = mzero
  -- | Substitute for all type variables.
  typeSubst_ :: (Var -> Builder TyCon) -> a -> a

-- | Substitute for all type variables in a `Typed`.
{-# INLINE typeSubst #-}
typeSubst :: (Typed a, Substitution s, SubstFun s ~ TyCon) => s -> a -> a
typeSubst s x = typeSubst_ (evalSubst s) x

-- | A wrapper for using the `Twee.Base.Symbolic` machinery on types.
newtype TypeView a = TypeView { unTypeView :: a }
instance Typed a => Symbolic (TypeView a) where
  type ConstantOf (TypeView a) = TyCon
  termsDL = fmap singleton . typesDL . unTypeView
  subst_ sub = TypeView . typeSubst_ sub . unTypeView
instance Typed a => Has (TypeView a) Type where
  the = typ . unTypeView

-- | All types that occur in a `Typed`.
typesDL :: Typed a => a -> DList Type
typesDL ty = return (typ ty) `mplus` otherTypesDL ty

-- | All type variables that occur in a `Typed`.
tyVars :: Typed a => a -> [Var]
tyVars = vars . TypeView

-- | Cast a `Typed` to a target type.
-- Succeeds if the target type is an instance of the current type.
cast :: Typed a => Type -> a -> Maybe a
cast ty x = do
  s <- match (typ x) ty
  return (typeSubst s x)

-- | Check if the second argument is an instance of the first argument.
matchType :: Type -> Type -> Maybe (Subst TyCon)
matchType = match

-- | Typed things that support function application.
class Typed a => Apply a where
  -- | Apply a function to its argument.
  --
  -- For most instances of `Typed`, the type of the argument must be exactly
  -- equal to the function's argument type. If you want unification to happen,
  -- use the `Typed` instance of `Poly`.
  tryApply :: a -> a -> Maybe a

-- | Apply a function to its argument, crashing on failure.
--
-- For most instances of `Typed`, the type of the argument must be exactly
-- equal to the function's argument type. If you want unification to happen,
-- use the `Typed` instance of `Poly`.
infixl `apply`
apply :: Apply a => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing ->
      error $
        "apply: ill-typed term: can't apply " ++
        prettyShow (typ f) ++ " to " ++ prettyShow (typ x)
    Just y -> y

-- | Check if a function can be applied to its argument.
canApply :: Apply a => a -> a -> Bool
canApply f x = isJust (tryApply f x)

-- Instances.
instance Typed Type where
  typ = id
  typeSubst_ = subst

instance Apply Type where
  tryApply (App (F Arrow) (Cons arg (Cons res Empty))) t
    | t == arg = Just res
  tryApply _ _ = Nothing

instance (Typed a, Typed b) => Typed (a, b) where
  typ (x, y) = build (app (fun (TyCon commaTyCon)) [typ x, typ y])
  otherTypesDL (x, y) = otherTypesDL x `mplus` otherTypesDL y
  typeSubst_ f (x, y) = (typeSubst_ f x, typeSubst_ f y)

instance (Typed a, Typed b) => Typed (Either a b) where
  typ (Left x)  = typ x
  typ (Right x) = typ x
  otherTypesDL (Left x)  = otherTypesDL x
  otherTypesDL (Right x) = otherTypesDL x
  typeSubst_ sub (Left x)  = Left  (typeSubst_ sub x)
  typeSubst_ sub (Right x) = Right (typeSubst_ sub x)

instance Typed a => Typed [a] where
  typ [] = typeOf ()
  typ (x:_) = typ x
  otherTypesDL [] = mzero
  otherTypesDL (x:xs) = otherTypesDL x `mplus` msum (map typesDL xs)
  typeSubst_ f xs = map (typeSubst_ f) xs

-- | Represents a forall-quantifier over all the type variables in a type.
-- Wrapping a term in @Poly@ normalises the type by alpha-renaming
-- type variables canonically.
--
-- The `Apply` instance for `Poly` does unification to handle applying a
-- polymorphic function.
newtype Poly a = Poly { unPoly :: a }
  deriving (Eq, Ord, Show, Pretty, Typeable)

-- | Build a `Poly`.
poly :: Typed a => a -> Poly a
poly x = Poly (canonicaliseType x)

-- | Alpha-rename type variables in a canonical way.
canonicaliseType :: Typed a => a -> a
canonicaliseType = unTypeView . canonicalise . TypeView

-- | Get the polymorphic type of a polymorphic value.
polyTyp :: Typed a => Poly a -> Poly Type
polyTyp (Poly x) = Poly (typ x)

-- | Rename the type variables of the second argument so that they don't overlap
-- with those of the first argument.
polyRename :: (Typed a, Typed b) => a -> Poly b -> b
polyRename x (Poly y) =
  unTypeView (renameAvoiding (TypeView x) (TypeView y))

-- | Rename the type variables of both arguments so that they don't overlap.
polyApply :: (Typed a, Typed b, Typed c) => (a -> b -> c) -> Poly a -> Poly b -> Poly c
polyApply f (Poly x) y = poly (f x (polyRename x y))

-- | Rename the type variables of both arguments so that they don't overlap.
polyPair :: (Typed a, Typed b) => Poly a -> Poly b -> Poly (a, b)
polyPair = polyApply (,)

-- | Rename the type variables of all arguments so that they don't overlap.
polyList :: Typed a => [Poly a] -> Poly [a]
polyList [] = poly []
polyList (x:xs) = polyApply (:) x (polyList xs)

-- | Find the most general unifier of two types.
polyMgu :: Poly Type -> Poly Type -> Maybe (Poly Type)
polyMgu ty1 ty2 = do
  let (ty1', ty2') = unPoly (polyPair ty1 ty2)
  sub <- unify ty1' ty2'
  return (poly (typeSubst sub ty1'))

instance Typed a => Typed (Poly a) where
  typ = typ . unPoly
  otherTypesDL = otherTypesDL . unPoly
  typeSubst_ f (Poly x) = poly (typeSubst_ f x)

instance Apply a => Apply (Poly a) where
  tryApply f x = do
    let (f', (x', resType)) = unPoly (polyPair f (polyPair x (poly (build (var (V 0))))))
    s <- unify (typ f') (arrowType [typ x'] resType)
    let (f'', x'') = typeSubst s (f', x')
    fmap poly (tryApply f'' x'')

-- | Convert an ordinary value to a dynamic value.
toPolyValue :: (Applicative f, Typeable a) => a -> Poly (Value f)
toPolyValue = poly . toValue . pure

-- | Dynamic values inside an applicative functor.
--
-- For example, a value of type @Value Maybe@ represents a @Maybe something@.
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

-- | Construct a `Value`.
toValue :: forall f (a :: *). Typeable a => f a -> Value f
toValue x = Value (typeRep (Proxy :: Proxy a)) (toAny x)

-- | Deconstruct a `Value`.
fromValue :: forall f (a :: *). Typeable a => Value f -> Maybe (f a)
fromValue x = do
  guard (typ x == typeRep (Proxy :: Proxy a))
  return (fromAny (value x))

instance Typed (Value f) where
  typ = valueType
  typeSubst_ f (Value ty x) = Value (typeSubst_ f ty) x
instance Applicative f => Apply (Value f) where
  tryApply f x = do
    ty <- tryApply (typ f) (typ x)
    return (Value ty (fromAny (value f) <*> value x))

-- | Unwrap a value to get at the thing inside, with an existential type.
unwrap :: Value f -> Unwrapped f
unwrap x =
  value x `In`
    Wrapper
      (\y -> Value (typ x) y)
      (\y ->
        if typ x == typ y
        then fromAny (value y)
        else error "non-matching types")

-- | The unwrapped value. Consists of the value itself (with an existential
-- type) and functions to wrap it up again.
data Unwrapped f where
  In :: f a -> Wrapper a -> Unwrapped f

-- | Functions for re-wrapping an `Unwrapped` value.
data Wrapper a =
  Wrapper {
    -- | Wrap up a value which has the same existential type as this one.
    wrap :: forall g. g a -> Value g,
    -- | Unwrap a value which has the same existential type as this one.
    reunwrap :: forall g. Value g -> g a }

-- | Apply a polymorphic function to a `Value`.
mapValue :: (forall a. f a -> g a) -> Value f -> Value g
mapValue f v =
  case unwrap v of
    x `In` w -> wrap w (f x)

-- | Apply a polymorphic function to a `Value`.
forValue :: Value f -> (forall a. f a -> g a) -> Value g
forValue x f = mapValue f x

-- | Apply a polymorphic function that returns a non-`Value` result to a `Value`.
ofValue :: (forall a. f a -> b) -> Value f -> b
ofValue f v =
  case unwrap v of
    x `In` _ -> f x

-- | Apply a polymorphic function that returns a non-`Value` result to a `Value`.
withValue :: Value f -> (forall a. f a -> b) -> b
withValue x f = ofValue f x

-- | Apply a polymorphic function to a pair of `Value`s.
pairValues :: forall f g. Typeable g => (forall a b. f a -> f b -> f (g a b)) -> Value f -> Value f -> Value f
pairValues f x y =
  ty `seq`
  Value {
    valueType = ty,
    value = toAny (f (value x) (value y)) }
  where
    ty = typeRep (Proxy :: Proxy g) `applyType` typ x `applyType` typ y

wrapFunctor :: forall f g h. Typeable h => (forall a. f a -> g (h a)) -> Value f -> Value g
wrapFunctor f x =
  ty `seq`
  Value {
    valueType = ty,
    value = toAny (f (value x)) }
  where
    ty = typeRep (Proxy :: Proxy h) `applyType` valueType x

unwrapFunctor :: forall f g h. Typeable g => (forall a. f (g a) -> h a) -> Value f -> Value h
unwrapFunctor f x =
  case typ x of
    App _ tys | tys@(_:_) <- unpack tys ->
      case ty `applyType` last tys == typ x of
        True ->
          Value {
            valueType = last tys,
            value = f (fromAny (value x)) }
        False ->
          error "non-matching types"
    _ -> error "value of type f a had wrong type"
  where
    ty = typeRep (Proxy :: Proxy g)

bringFunctor :: Functor f => Value f -> f (Value Identity)
bringFunctor val =
  case unwrap val of
    x `In` w ->
      fmap (wrap w . Identity) x
