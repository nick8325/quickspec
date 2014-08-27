-- | A relation between types and values.
--   @'TypeRel' f@ relates each type @a@ to a set of values
--   of type @f a@.

{-# LANGUAGE CPP, Rank2Types, TypeOperators #-}
module Test.QuickSpec.Utils.TypeRel where

#include "errors.h"
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import Test.QuickSpec.Utils.TypeMap(TypeMap)
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.Typeable
import Data.Maybe
import Test.QuickSpec.Utils

type TypeRel f = TypeMap (List `O` f)

empty :: TypeRel f
empty = TypeMap.empty

singleton :: Typeable a => f a -> TypeRel f
singleton x = TypeMap.singleton (O [x])

fromList :: [Some f] -> TypeRel f
fromList = TypeMap.fromList . classify

toList :: TypeRel f -> [Some f]
toList = concatMap disperse . TypeMap.toList

lookup :: Typeable a => a -> TypeRel f -> [f a]
lookup x m = unO (TypeMap.lookup (O []) x m)

mapValues :: (forall a. Typeable a => f a -> g a) -> TypeRel f -> TypeRel g
mapValues f = TypeMap.mapValues2 (map f)

gather :: [Some f] -> Some (List `O` f)
gather [] = ERROR "empty list"
gather (Some x:xs) = Some (O (x:map gcast' xs))
  where gcast' (Some y) =
          fromMaybe (ERROR msg) (gcast y)
        msg = "heterogeneous list"

disperse :: Some (List `O` f) -> [Some f]
disperse (Some (O xs)) = map Some xs

classify :: [Some f] -> [Some (List `O` f)]
classify xs = map gather (partitionBy someType xs)
