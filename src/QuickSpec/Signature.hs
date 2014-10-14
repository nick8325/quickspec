-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, Rank2Types, StandaloneDeriving, TypeOperators, FlexibleContexts, KindSignatures, GeneralizedNewtypeDeriving, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module QuickSpec.Signature where

#include "errors.h"
import Data.Constraint
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Prop
import Data.Functor.Identity
import Data.Monoid
import Test.QuickCheck hiding (subterms)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Char hiding (ord)
import Data.Maybe
import Control.Applicative

newtype Instance = Instance { unInstance :: [Value Instance1] } deriving (Monoid, Show)
newtype Instance1 a = Instance1 (Value (Instance2 a))
data Instance2 a b = Instance2 (b -> a)

makeInstance :: forall a b. (Typeable a, Typeable b) => (b -> a) -> Instance
makeInstance f =
  case typeOf (undefined :: a) of
    Fun Arrow _ ->
      ERROR "makeInstance: curried functions not supported"
    _ ->
      Instance [toValue (Instance1 (toValue (Instance2 f)))]

deriving instance Typeable Ord
deriving instance Typeable Arbitrary
deriving instance Typeable CoArbitrary
deriving instance Typeable (() :: Constraint)

data Signature =
  Signature {
    constants  :: [Constant],
    instances  :: [Instance],
    background :: [Prop],
    defaultTo  :: [Type] }
  deriving Show

defaultTo_ :: Signature -> Type
defaultTo_ sig =
  case defaultTo sig of
    [] -> typeOf (undefined :: Int)
    [ty]
      | null (vars ty) -> ty
      | otherwise ->
        error $ "Default type is not ground: " ++ prettyShow ty
    tys -> error $ "Several default types specified: " ++ prettyShow tys

instances_ :: Signature -> [Value Instance1]
instances_ sig = concatMap unInstance (instances sig ++ defaultInstances)

defaultInstances :: [Instance]
defaultInstances = [
  inst (Sub Dict :: Arbitrary A :- Arbitrary [A]),
  inst (Sub Dict :: Ord A :- Ord [A]),
  inst (Sub Dict :: CoArbitrary A :- CoArbitrary [A]),
  baseType (undefined :: Int),
  baseType (undefined :: Integer),
  baseType (undefined :: Bool),
  inst (Sub Dict :: () :- CoArbitrary Int),
  inst (Sub Dict :: () :- CoArbitrary Integer),
  inst (Sub Dict :: () :- CoArbitrary Bool),
  inst2 (Sub Dict :: (CoArbitrary A, Arbitrary B) :- Arbitrary (A -> B)),
  makeInstance (\() -> Dict :: Dict ()),
  makeInstance (\(dict :: Dict (Ord A)) -> DictOf dict),
  makeInstance (\(dict :: Dict (Arbitrary A)) -> DictOf dict),
  names1 (\(NamesFor names :: NamesFor A) ->
            NamesFor (map (++ "s") names) :: NamesFor [A]),
  names (NamesFor ["n", "m", "o"] :: NamesFor Int),
  names (NamesFor ["n", "m", "o"] :: NamesFor Integer),
  names (NamesFor ["p", "q", "r"] :: NamesFor (A -> Bool)),
  names (NamesFor ["f", "g", "h"] :: NamesFor (A -> B)),
  names (NamesFor ["x", "y", "z"] :: NamesFor A)]

namesFor_ :: Signature -> Type -> [String]
namesFor_ sig ty =
  case findInstanceOf sig ty of
    (x:_) -> ofValue unNamesFor x

newtype NamesFor a = NamesFor { unNamesFor :: [String] } deriving Typeable
newtype DictOf c a = DictOf { unDictOf :: Dict (c a) } deriving Typeable

instance Monoid Signature where
  mempty = Signature [] [] [] []
  Signature cs is b d `mappend` Signature cs' is' b' d' = Signature (cs++cs') (is++is') (b++b') (d `mappend` d')

signature :: Signature
signature = mempty

constant :: Typeable a => String -> a -> Constant
constant name x = Constant name value (poly value) (arity (typeOf x)) style
  where
    value = toValue (Identity x)
    style
      | head name == ',' = Tuple (arity (typeOf x))
      | isOp name = Infix 5
      | otherwise = Curried

isOp :: String -> Bool
isOp "[]" = False
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_'

baseType :: forall a. (Ord a, Arbitrary a, Typeable a) => a -> Instance
baseType _ =
  mconcat [
    inst (Sub Dict :: () :- Ord a),
    inst (Sub Dict :: () :- Arbitrary a)]

inst :: forall c1 c2. (Typeable c1, Typeable c2) => c1 :- c2 -> Instance
inst ins = makeInstance f
  where
    f :: Dict c1 -> Dict c2
    f Dict = case ins of Sub dict -> dict

inst2 :: forall c1 c2 c3. (Typeable c1, Typeable c2, Typeable c3) => (c1, c2) :- c3 -> Instance
inst2 ins = makeInstance f
  where
    f :: (Dict c1, Dict c2) -> Dict c3
    f (Dict, Dict) = case ins of Sub dict -> dict

names  :: Typeable a => NamesFor a -> Instance
names x = makeInstance (\() -> x)

names1 :: (Typeable a, Typeable b) => (a -> NamesFor b) -> Instance
names1 = makeInstance

typeUniverse :: Signature -> Set Type
typeUniverse sig =
  Set.fromList $
    Var (TyVar 0):
    [ oneTypeVar (typ t) | c <- constants sig, t <- subterms (typ c) ]

findInstanceOf :: forall f. Typeable f => Signature -> Type -> [Value f]
findInstanceOf sig ty =
  map (unwrapFunctor runIdentity) (findInstance sig ty')
  where
    ty' = typeRep (undefined :: proxy f) `applyType` ty

findInstance :: Signature -> Type -> [Value Identity]
findInstance sig (Fun unit [])
  | unit == tyCon () =
    return (toValue (Identity ()))
findInstance sig (Fun pair [ty1, ty2])
  | pair == tyCon ((),()) = do
    x <- findInstance sig ty1
    y <- findInstance sig ty2
    return (pairValues (liftA2 (,)) x y)
findInstance sig ty = do
  i <- instances_ sig
  sub <- maybeToList (match (typ i) ty)
  let i' = typeSubst (evalSubst sub) i
  case unwrap i' of
    Instance1 i1 `In` w1 -> do
      let i1' = typeSubst (evalSubst sub) i1
      case unwrap i1' of
        Instance2 f `In` w2 -> do
          x <- fmap (reunwrap w2) (findInstance sig (typ i1'))
          return (wrap w1 (fmap f x))
