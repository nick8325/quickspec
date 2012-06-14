{-# LANGUAGE Rank2Types, ExistentialQuantification #-}
module Typed where

import Control.Monad
import Typeable
import Data.Maybe
import Utils

data Some f = forall a. Typeable a => Some (f a)

newtype K a b = K a
newtype C f g a = C { unC :: f (g a) }

newtype Witnessed a = Witnessed { witness :: a }
type Witness = Some Witnessed

witnessArrow :: (Typeable a, Typeable b) => a -> b -> (a -> b)
witnessArrow = undefined

some :: (forall a. Typeable a => f a -> b) -> Some f -> b
some f (Some x) = f x

mapSome :: (forall a. Typeable a => f a -> g a) -> Some f -> Some g
mapSome f (Some x) = Some (f x)

mapSomeM :: Monad m => (forall a. Typeable a => f a -> m (g a)) -> Some f -> m (Some g)
mapSomeM f (Some x) = liftM Some (f x)

someType :: Some f -> TypeRep
someType (Some x) = typeOf (witness x)
  where witness :: f a -> a
        witness = undefined

gather :: [Some f] -> Some (C [] f)
gather [] = error "Typed.sequence: empty list"
gather (Some x:xs) = Some (C (x:map gcast' xs))
  where gcast' (Some y) = fromMaybe (error msg) (gcast y)
        msg = "Typed.gather: heterogeneous list"

disperse :: Some (C [] f) -> [Some f]
disperse (Some (C xs)) = map Some xs

classify :: [Some f] -> [Some (C [] f)]
classify xs = map gather (partitionBy someType xs)
