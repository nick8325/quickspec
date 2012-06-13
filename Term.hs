{-# LANGUAGE Rank2Types, ExistentialQuantification, DeriveDataTypeable #-}
module Term where

import Data.Typeable
import Test.QuickCheck
import Typed
import Data.Function
import Data.Ord

data Named a = Named {
  name :: String,
  index :: Int,
  typ_ :: TypeRep,
  the :: a
  } deriving Typeable

instance Eq (Named a) where
  (==) = (==) `on` index

instance Ord (Named a) where
  compare = comparing index

type Name = Named ()

erase :: Named a -> Name
erase (Named name index typ_ _) = Named name index typ_ ()

data Term a =
    Var (Var a)
  | Const (Named a)
  | forall b. App (Term (b -> a)) (Term b) deriving Typeable

type Var a = Named (Gen a)

-- Generate a random variable valuation
valuation :: Gen (Var a -> a)
valuation = promote (\x -> index x `variant'` the x)
  where -- work around the fact that split doesn't work
        variant' 0 = variant 0
        variant' n = variant (-1) . variant' (n-1)

eval :: (forall a. Var a -> a) -> Term a -> a
eval env (Var x) = env x
eval env (Const x) = the x
eval env (App f x) = eval env f (eval env x)

indices :: Term a -> [Int]
indices t = indices' t []
  where indices' :: Term a -> [Int] -> [Int]
        indices' (Var x) = (index x:)
        indices' (Const x) = (index x:)
        indices' (App f x) = indices' f . indices' x

depth :: Term a -> Int
depth (App f x) = depth f `max` (1 + depth x)
depth _ = 0

holes :: Term a -> [(Name, Int)]
holes t = holes' 0 t []
  where holes' :: Int -> Term a -> [(Name, Int)] -> [(Name, Int)]
        holes' d (Var x) = ((erase x, d):)
        holes' d Const{} = id
        holes' d (App f x) = holes' d f . holes' (d+1) x
