{-# LANGUAGE Rank2Types, ExistentialQuantification, DeriveDataTypeable, StandaloneDeriving, DeriveFunctor #-}
module Typed where

import Control.Monad
import Data.Map(Map)
import qualified Data.Map as Map
import Typeable
import qualified Data.Typeable as T
import Data.Maybe
import Utils

data Some f = forall a. Typeable a => Some (f a)

newtype K a b = K a
newtype C f g a = C { unC :: f (g a) } deriving Functor

data CType = CType deriving Typeable

instance (Typeable1 f, Typeable1 g) => Typeable1 (C f g) where
  typeOf1 ~(C x) =
    unTypeRep $
    mkTyConApp (typeRepTyCon (typeOf CType)) [ typeOf1 x ]

some :: (forall a. Typeable a => f a -> b) -> Some f -> b
some f (Some x) = f x

mapSome :: (forall a. Typeable a => f a -> g a) -> Some f -> Some g
mapSome f (Some x) = Some (f x)

mapSomeM :: Monad m => (forall a. Typeable a => f a -> m (g a)) -> Some f -> m (Some g)
mapSomeM f (Some x) = liftM Some (f x)

typ :: Some f -> TypeRep
typ (Some x) = typeOf (witness x)
  where witness :: f a -> a
        witness = undefined

gather :: Typeable1 f => [Some f] -> Some (C [] f)
gather [] = error "Typed.sequence: empty list"
gather (Some x:xs) = Some (C (x:map cast' xs))
  where cast' (Some y) = fromMaybe (error msg) (cast y)
        msg = "Typed.gather: heterogeneous list"

disperse :: Typeable1 f => Some (C [] f) -> [Some f]
disperse (Some (C xs)) = map Some xs

classify :: Typeable1 f => [Some f] -> [Some (C [] f)]
classify xs = map gather (partitionBy typ xs)

type TypeMap f = Map TypeRep (Some f)

empty :: TypeMap f
empty = fromList []

fromList :: [Some f] -> TypeMap f
fromList xs = Map.fromList [ (typ x, x) | x <- xs ]

toList :: TypeMap f -> [Some f]
toList = Map.elems

lookup :: (Typeable1 f, Typeable a) => f a -> a -> TypeMap f -> f a
lookup def x m =
  case Map.lookup (typeOf x) m of
    Nothing -> def
    Just (Some y) ->
      case cast y of
        Nothing -> error "Typed.lookup: type error"
        Just z -> z

mapValues :: (forall a. Typeable a => f a -> g a) -> TypeMap f -> TypeMap g
mapValues f = fmap (mapSome f)

