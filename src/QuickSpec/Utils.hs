-- | Miscellaneous utility functions.

{-# LANGUAGE CPP #-}
module QuickSpec.Utils where

import Control.Arrow((&&&))
import Control.Exception
import Control.Spoon
import Data.List(groupBy, sortBy)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif
import Data.Ord(comparing)
import System.IO

repeatM :: Monad m => m a -> m [a]
repeatM = sequence . repeat

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value =
  map (map fst) .
  groupBy (\x y -> snd x == snd y) .
  sortBy (comparing snd) .
  map (id &&& value)

collate :: Ord a => ([b] -> c) -> [(a, b)] -> [(a, c)]
collate f = map g . partitionBy fst
  where
    g xs = (fst (head xs), f (map snd xs))

isSorted :: Ord a => [a] -> Bool
isSorted xs = and (zipWith (<=) xs (tail xs))

isSortedBy :: Ord b => (a -> b) -> [a] -> Bool
isSortedBy f xs = isSorted (map f xs)

usort :: Ord a => [a] -> [a]
usort = usortBy compare

usortBy :: (a -> a -> Ordering) -> [a] -> [a]
usortBy f = map head . groupBy (\x y -> f x y == EQ) . sortBy f

sortBy' :: Ord b => (a -> b) -> [a] -> [a]
sortBy' f = map snd . sortBy (comparing fst) . map (\x -> (f x, x))

usortBy' :: Ord b => (a -> b) -> [a] -> [a]
usortBy' f = map snd . usortBy (comparing fst) . map (\x -> (f x, x))

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

minimumBy :: (a -> a -> Bool) -> [a] -> a
minimumBy f = foldr1 (\x y -> if f x y then x else y)

instance Ord a => Monoid (Min a) where
  mempty = Min Nothing
  Min (Just x) `mappend` y = Min (Just (getMinWith x y))
  Min Nothing  `mappend` y = y

labelM :: Monad m => (a -> m b) -> [a] -> m [(a, b)]
labelM f = mapM (\x -> do { y <- f x; return (x, y) })

#if __GLASGOW_HASKELL__ < 710
isSubsequenceOf :: Ord a => [a] -> [a] -> Bool
[] `isSubsequenceOf` ys = True
(x:xs) `isSubsequenceOf` [] = False
(x:xs) `isSubsequenceOf` (y:ys)
  | x == y = xs `isSubsequenceOf` ys
  | otherwise = (x:xs) `isSubsequenceOf` ys
#endif
