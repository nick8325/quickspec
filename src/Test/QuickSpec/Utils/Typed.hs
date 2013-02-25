-- | Functions for working with existentially-quantified types
--   and similar.

{-# LANGUAGE CPP, Rank2Types, ExistentialQuantification, TypeOperators, TypeSynonymInstances, FlexibleInstances #-}
module Test.QuickSpec.Utils.Typed where

#include "../errors.h"
import Control.Monad
import Test.QuickSpec.Utils.Typeable
import Data.Ord
import Data.Function
import Data.Maybe

data Some f = forall a. Typeable a => Some (f a)

newtype O f g a = O { unO :: f (g a) }
type List = []

newtype Witnessed a = Witness { witness :: a }
type Witness = Some Witnessed

-- No Typeable (Witnessed a) instance to save accidentally looking up
-- Witnessed a instead of a in a TypeMap

instance Eq Witness where
  (==) = (==) `on` witnessType

instance Ord Witness where
  compare = comparing witnessType

instance Show Witness where
  show = show . witnessType

witnessType :: Witness -> TypeRep
witnessType = some (typeOf . witness)

data Tagged a = Tagged { tag :: Witness, erase :: a }

tagged :: Typeable a => (f a -> b) -> f a -> Tagged b
tagged f x = Tagged (Some (Witness (witness x))) (f x)
  where witness :: f a -> a
        witness = undefined

some :: (forall a. Typeable a => f a -> b) -> Some f -> b
some f (Some x) = f x

some2 :: (forall a. Typeable a => f (g a) -> b) -> Some (f `O` g) -> b
some2 f = some (f . unO)

mapSome :: (forall a. Typeable a => f a -> g a) -> Some f -> Some g
mapSome f (Some x) = Some (f x)

mapSome2 :: (forall a. Typeable a => f (g a) -> h (i a)) -> Some (f `O` g) -> Some (h `O` i)
mapSome2 f = mapSome (O . f . unO)

mapSomeM :: Monad m => (forall a. Typeable a => f a -> m (g a)) -> Some f -> m (Some g)
mapSomeM f (Some x) = liftM Some (f x)

someType :: Some f -> TypeRep
someType (Some x) = typeOf (witness x)
  where witness :: f a -> a
        witness = undefined

someWitness :: Some f -> Witness
someWitness = mapSome (const undefined)

splitArrow :: TypeRep -> Maybe (TypeRep, TypeRep)
splitArrow ty =
  case splitTyConApp ty of
    (c, [lhs, rhs]) | c == arr -> Just (lhs, rhs)
    _ -> Nothing
  where (arr, _) = splitTyConApp (typeOf (undefined :: Int -> Int))

rightArrow :: TypeRep -> TypeRep
rightArrow ty = snd (fromMaybe (ERROR msg) (splitArrow ty))
  where
    msg = "type oversaturated"
