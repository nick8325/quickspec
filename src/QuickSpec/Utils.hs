-- | Miscellaneous utility functions.

module QuickSpec.Utils where

import Control.Arrow((&&&))
import Data.List(groupBy, sortBy)
import Data.Ord(comparing)
import System.IO
import Control.Exception
import Control.Spoon
import Data.Monoid

repeatM :: Monad m => m a -> m [a]
repeatM = sequence . repeat

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value =
  map (map fst) .
  groupBy (\x y -> snd x == snd y) .
  sortBy (comparing snd) .
  map (id &&& value)

isSorted :: Ord a => [a] -> Bool
isSorted xs = and (zipWith (<=) xs (tail xs))

isSortedBy :: Ord b => (a -> b) -> [a] -> Bool
isSortedBy f xs = isSorted (map f xs)

usort :: Ord a => [a] -> [a]
usort = usortBy compare

usortBy :: (a -> a -> Ordering) ->[a] -> [a]
usortBy f = map head . groupBy (\x y -> f x y == EQ) . sortBy f

orElse :: Ordering -> Ordering -> Ordering
EQ `orElse` x = x
x  `orElse` _ = x

unbuffered :: IO a -> IO a
unbuffered x = do
  buf <- hGetBuffering stdout
  bracket_
    (hSetBuffering stdout NoBuffering)
    (hSetBuffering stdout buf)
    x

spoony :: Eq a => a -> Maybe a
spoony x = teaspoon ((x == x) `seq` x)

newtype Max a = Max { getMax :: Maybe a }

getMaxWith :: Ord a => a -> Max a -> a
getMaxWith x (Max (Just y)) = x `max` y
getMaxWith x (Max Nothing)  = x

instance Ord a => Monoid (Max a) where
  mempty = Max Nothing
  Max (Just x) `mappend` y = Max (Just (getMaxWith x y))
  Max Nothing  `mappend` y = y

newtype Min a = Min { getMin :: Maybe a }

getMinWith :: Ord a => a -> Min a -> a
getMinWith x (Min (Just y)) = x `min` y
getMinWith x (Min Nothing)  = x

instance Ord a => Monoid (Min a) where
  mempty = Min Nothing
  Min (Just x) `mappend` y = Min (Just (getMinWith x y))
  Min Nothing  `mappend` y = y

labelM :: Monad m => (a -> m b) -> [a] -> m [(a, b)]
labelM f = mapM (\x -> do { y <- f x; return (x, y) })

isSubsequenceOf :: Ord a => [a] -> [a] -> Bool
[] `isSubsequenceOf` ys = True
(x:xs) `isSubsequenceOf` [] = False
(x:xs) `isSubsequenceOf` (y:ys)
  | x == y = xs `isSubsequenceOf` ys
  | otherwise = (x:xs) `isSubsequenceOf` ys
