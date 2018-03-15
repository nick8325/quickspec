{-# LANGUAGE ScopedTypeVariables,DeriveDataTypeable #-}

import Prelude hiding (null)
import QuickSpec
import Test.QuickCheck
import Test.QuickCheck.Poly(OrdA(..))
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

main = quickSpec [
  prelude `without` ["*"],
  monoType (Proxy :: Proxy OrdA),
  monoTypeWithVars ["h", "h1", "h2"] (Proxy :: Proxy (Heap OrdA)),

  "nil"        `con` (Nil        :: Heap OrdA),
  "insert"     `con` (insert     :: OrdA -> Heap OrdA -> Heap OrdA),
  "findMin"    `con` (findMin    :: Heap OrdA -> OrdA),
  "deleteMin"  `con` (deleteMin  :: Heap OrdA -> Heap OrdA),
  "merge"      `con` (merge      :: Heap OrdA -> Heap OrdA -> Heap OrdA),
  "null"       `con` (null       :: Heap OrdA -> Bool),
  "fromList"   `con` (fromList   :: [OrdA] -> Heap OrdA),
  con "True" True,
  con "False" False,

  -- A few more list functions that are helpful for getting
  -- laws about toList/fromList.
  -- We use "background" to mark the functions as background theory,
  -- so that we only get laws that involve one of the heap functions.
  background [
  "head" `con` (head :: [A] -> A),
  "tail" `con` (tail :: [A] -> [A]),
  "toList"     `con` (toList     :: Heap OrdA -> [OrdA]),
  "sort"       `con` (L.sort     :: [OrdA] -> [OrdA]),
  "insertList" `con` (L.insert   :: OrdA -> [OrdA] -> [OrdA]),
  "nullList"   `con` (L.null     :: [OrdA] -> Bool),
  "deleteList" `con` (L.delete   :: OrdA -> [OrdA] -> [OrdA]),
  "mergeLists" `con` (mergeLists :: [OrdA] -> [OrdA] -> [OrdA])]]
