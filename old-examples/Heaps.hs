{-# LANGUAGE ScopedTypeVariables,DeriveDataTypeable #-}

import Prelude hiding (null)
import Test.QuickSpec
import Test.QuickCheck
import Data.Typeable
import Data.Ord
import qualified Data.List as L

data Heap a = Nil | Branch Int a (Heap a) (Heap a) deriving Typeable

instance Ord a => Eq (Heap a) where
  h1 == h2 = toList h1 == toList h2

instance Ord a => Ord (Heap a) where
  compare = comparing toList

instance (Ord a, Arbitrary a) => Arbitrary (Heap a) where
  arbitrary = fmap fromList arbitrary

toList :: Ord a => Heap a -> [a]
toList h | null h = []
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

mergeLists :: Ord a => [a] -> [a] -> [a]
mergeLists [] xs = xs
mergeLists xs [] = xs
mergeLists (x:xs) (y:ys)
  | x < y = x:mergeLists xs (y:ys)
  | otherwise = y:mergeLists (x:xs) ys

heaps :: forall a. (Ord a, Typeable a, Arbitrary a) => a -> [Sig]
heaps a = [
  prelude a,

  ["h", "h1", "h2"] `vars` (undefined :: Heap a),

  "nil"        `fun0` (Nil        :: Heap a),
  "insert"     `fun2` (insert     :: a -> Heap a -> Heap a),
  "findMin"    `fun1` (findMin    :: Heap a -> a),
  "deleteMin"  `fun1` (deleteMin  :: Heap a -> Heap a),
  "merge"      `fun2` (merge      :: Heap a -> Heap a -> Heap a),
  "null"       `fun1` (null       :: Heap a -> Bool),
  "fromList"   `fun1` (fromList   :: [a] -> Heap a),

  -- A few more list functions that are helpful for getting
  -- laws about toList/fromList.
  -- We use "background" to mark the functions as background theory,
  -- so that we only get laws that involve one of the heap functions.
  -- toList is marked as background to make the presentation of the
  -- equations a bit prettier: laws about e.g. findMin and toList
  -- will appear in QuickSpec's "Equations about findMin" section
  -- rather than "Equations about several functions".
  background [
  "toList"     `fun1` (toList     :: Heap a -> [a]),
  "sort"       `fun1` (L.sort     :: [a] -> [a]),
  "insertList" `fun2` (L.insert   :: a -> [a] -> [a]),
  "nullList"   `fun1` (L.null     :: [a] -> Bool),
  "deleteList" `fun2` (L.delete   :: a -> [a] -> [a]),
  "mergeLists" `fun2` (mergeLists :: [a] -> [a] -> [a])]]

main = quickSpec (heaps (undefined :: A))
