module Utils where

import Control.Arrow((&&&))
import Data.List(groupBy, sortBy, group, sort)
import Data.Ord(comparing)

repeatM :: Monad m => m a -> m [a]
repeatM = sequence . repeat

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value = map (map fst) . groupBy (\x y -> snd x == snd y) . sortBy (comparing snd) . map (id &&& value)

isSorted :: Ord a => [a] -> Bool
isSorted xs = and (zipWith (<=) xs (tail xs))

isSortedBy :: Ord b => (a -> b) -> [a] -> Bool
isSortedBy f xs = isSorted (map f xs)

usort :: Ord a => [a] -> [a]
usort = map head . group . sort

merge :: Ord b => (a -> a -> a) -> (a -> b) -> [a] -> [a] -> [a]
merge f c = aux
  where aux [] ys = ys
        aux xs [] = xs
        aux (x:xs) (y:ys) =
          case comparing c x y of
            LT -> x:aux xs (y:ys)
            GT -> y:aux (x:xs) ys
            EQ -> f x y:aux xs ys
