-- TODO: write wrapper around TypeRep to get around lack of Ord
-- instance in old GHC versions + bug

{-# LANGUAGE Rank2Types, ExistentialQuantification #-}
module Typed where

import Control.Monad
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Typeable
import Data.Maybe
import Utils

data Some f = forall a. (Ord a, Typeable a) => Some (f a)

some :: (forall a. f a -> b) -> Some f -> b
some f (Some x) = f x

mapSome :: (forall a. f a -> g a) -> Some f -> Some g
mapSome f (Some x) = Some (f x)

mapSomeM :: Monad m => (forall a. f a -> m (g a)) -> Some f -> m (Some g)
mapSomeM f (Some x) = liftM Some (f x)

typ :: Some f -> TypeRep
typ (Some x) = typeOf (witness x)
  where witness :: f a -> a
        witness = undefined

newtype List f a = List { unList :: [f a] }

sequence :: Typeable1 f => [Some f] -> Some (List f)
sequence [] = error "Typed.sequence: empty list"
sequence (Some x:xs) = Some (List (x:map cast' xs))
  where cast' (Some y) = fromMaybe (error msg) (cast y)
        msg = "Typed.sequence: heterogeneous list"

classify :: Typeable1 f => [Some f] -> [Some (List f)]
classify xs = map Typed.sequence (partitionBy typ xs)

type TypeMap f = Map TypeRep (Some f)

fromList :: [Some f] -> TypeMap f
fromList xs = Map.fromList [ (typ x, x) | x <- xs ]

lookup :: Typeable1 f => Typeable a => f a -> a -> TypeMap f -> f a
lookup def x m =
  case Map.lookup (typeOf x) m of
    Nothing -> def
    Just (Some y) ->
      case cast y of
        Nothing -> error "Typed.lookup: type error"
        Just z -> z

mapValues :: (forall a. f a -> g a) -> TypeMap f -> TypeMap g
mapValues f = fmap (mapSome f)
