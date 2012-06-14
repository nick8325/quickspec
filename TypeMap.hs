{-# LANGUAGE Rank2Types #-}
module TypeMap where

import qualified Data.Map as Map
import Data.Map(Map)
import Typed
import Typeable

type TypeMap f = Map TypeRep (Some f)

empty :: TypeMap f
empty = fromList []

singleton :: Typeable a => f a -> TypeMap f
singleton x = fromList [Some x]

fromList :: [Some f] -> TypeMap f
fromList xs = Map.fromList [ (someType x, x) | x <- xs ]

toList :: TypeMap f -> [Some f]
toList = Map.elems

lookup :: Typeable a => f a -> a -> TypeMap f -> f a
lookup def x m =
  case Map.lookup (typeOf x) m of
    Nothing -> def
    Just (Some y) ->
      case gcast y of
        Nothing -> error "Typed.lookup: type error"
        Just z -> z

mapValues :: (forall a. Typeable a => f a -> g a) -> TypeMap f -> TypeMap g
mapValues f = fmap (mapSome f)
