{-# LANGUAGE ScopedTypeVariables,DeriveDataTypeable #-}
module Heaps where

import Test.QuickSpec
import Test.QuickCheck
import Data.Typeable
import Data.Ord

data Heap a = Nil | Branch Int a (Heap a) (Heap a) deriving Typeable

instance Ord a => Eq (Heap a) where
  h1 == h2 = toList h1 == toList h2

instance Ord a => Ord (Heap a) where
  compare = comparing toList

instance (Ord a, Arbitrary a) => Arbitrary (Heap a) where
  arbitrary = fmap fromList arbitrary

toList :: Ord a => Heap a -> [a]
toList h | Heaps.null h = []
         | otherwise = findMin h:toList (deleteMin h)

fromList :: Ord a => [a] -> Heap a
fromList = foldr insert Nil

null :: Heap a -> Bool
null Nil = True
null _ = False

findMin :: Heap a -> a
findMin (Branch _ x _ _) = x

insert :: Ord a => a -> Heap a -> Heap a
insert x h = merge h (branch x Nil Nil)

deleteMin :: Ord a => Heap a -> Heap a
deleteMin (Branch _ _ l r) = merge l r

branch :: Ord a => a -> Heap a -> Heap a -> Heap a
branch x l r | npl l <= npl r = Branch (npl l + 1) x l r
             | otherwise = Branch (npl r + 1) x r l

merge :: Ord a => Heap a -> Heap a -> Heap a
merge Nil h = h
merge h Nil = h
merge h1@(Branch _ x1 l1 r1) h2@(Branch _ x2 l2 r2)
 | x1 <= x2 = branch x1 (merge l1 h2) r1
 | otherwise = merge h2 h1

npl :: Heap a -> Int
npl Nil = 0
npl (Branch n _ _ _) = n

heaps :: forall a. (Ord a, Typeable a, Arbitrary a) => a -> [Sig]
heaps _ = [
  vars ["h", "h1", "h2"] (undefined :: Heap a),
  fun1 "toList" (toList :: Heap a -> [a]),
  fun1 "fromList" (fromList :: [a] -> Heap a),
  fun1 "null" (Heaps.null :: Heap a -> Bool),
  fun1 "findMin" (findMin :: Heap a -> a),
  fun2 "insert" (insert :: a -> Heap a -> Heap a),
  fun1 "deleteMin" (deleteMin :: Heap a -> Heap a),
  fun2 "merge" (merge :: Heap a -> Heap a -> Heap a),
  fun0 "nil" (Nil :: Heap a)]
