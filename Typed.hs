{-# LANGUAGE Rank2Types, ExistentialQuantification, TypeOperators #-}
module Typed where

import Control.Monad
import Typeable
import Data.Maybe
import Utils

data Some f = forall a. Typeable a => Some (f a)

newtype O f g a = O { unO :: f (g a) }
type List = []

newtype Witnessed a = Witnessed { witness :: a }
type Witness = Some Witnessed

data Typed a = Typed { typ :: Witness, erase :: a }

tag :: Typeable a => (f a -> b) -> f a -> Typed b
tag f x = Typed (Some (Witnessed (witness x))) (f x)
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

gather :: [Some f] -> Some (List `O` f)
gather [] = error "Typed.sequence: empty list"
gather (Some x:xs) = Some (O (x:map gcast' xs))
  where gcast' (Some y) = fromMaybe (error msg) (gcast y)
        msg = "Typed.gather: heterogeneous list"

disperse :: Some (List `O` f) -> [Some f]
disperse (Some (O xs)) = map Some xs

classify :: [Some f] -> [Some (List `O` f)]
classify xs = map gather (partitionBy someType xs)
