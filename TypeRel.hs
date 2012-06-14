{-# LANGUAGE Rank2Types #-}
module TypeRel where

import qualified TypeMap
import TypeMap(TypeMap)
import Typed
import Typeable

type TypeRel f = TypeMap (C [] f)

empty :: TypeRel f
empty = TypeMap.empty

singleton :: Typeable a => f a -> TypeRel f
singleton x = TypeMap.singleton (C [x])

fromList :: [Some f] -> TypeRel f
fromList = TypeMap.fromList . classify

toList :: TypeRel f -> [Some f]
toList = concatMap disperse . TypeMap.toList

lookup :: Typeable a => a -> TypeRel f -> [f a]
lookup x m = unC (TypeMap.lookup (C []) x m)

mapValues :: (forall a. Typeable a => f a -> g a) -> TypeRel f -> TypeRel g
mapValues f = TypeMap.mapValues (C . map f . unC)
