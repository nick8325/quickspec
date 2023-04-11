-- A stress test using lots and lots of list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds, FlexibleContexts #-}
import QuickSpec
import QuickSpec.Internal.Utils
import Data.List
import Control.Monad
import Test.QuickCheck.Poly

main = quickSpec [
  con "length" (length :: [OrdA] -> Int),
  con "sort" (sort :: [Int] -> [Int]),
  con "scanr" (scanr :: (OrdA -> OrdA -> OrdA) -> OrdA -> [OrdA] -> [OrdA]),
  con "succ" (succ :: Int -> Int),
  con ">>=" ((>>=) :: [OrdA] -> (OrdA -> [OrdA]) -> [OrdA]),
  con "snd" (snd :: (OrdA, OrdA) -> OrdA),
  con "reverse" (reverse :: [OrdA] -> [OrdA]),
  con "0" (0 :: Int),
  con "," ((,) :: OrdA -> OrdA -> (OrdA, OrdA)),
  con ">=>" ((>=>) :: (OrdA -> [OrdA]) -> (OrdA -> [OrdA]) -> OrdA -> [OrdA]),
  con ":" ((:) :: OrdA -> [OrdA] -> [OrdA]),
  con "break" (break :: (OrdA -> Bool) -> [OrdA] -> ([OrdA], [OrdA])),
  con "filter" (filter :: (OrdA -> Bool) -> [OrdA] -> [OrdA]),
  con "scanl" (scanl :: (OrdA -> OrdA -> OrdA) -> OrdA -> [OrdA] -> [OrdA]),
  con "zipWith" (zipWith :: (OrdA -> OrdA -> OrdA) -> [OrdA] -> [OrdA] -> [OrdA]),
  con "concat" (concat :: [[OrdA]] -> [OrdA]),
  con "zip" (zip :: [OrdA] -> [OrdA] -> [(OrdA, OrdA)]),
  con "usort" (usort :: [Int] -> [Int]),
  con "sum" (sum :: [Int] -> Int),
  con "++" ((++) :: [OrdA] -> [OrdA] -> [OrdA]),
  con "map" (map :: (OrdA -> OrdA) -> [OrdA] -> [OrdA]),
  con "foldl" (foldl :: (OrdA -> OrdA -> OrdA) -> OrdA -> [OrdA] -> OrdA),
  con "takeWhile" (takeWhile :: (OrdA -> Bool) -> [OrdA] -> [OrdA]),
  con "foldr" (foldr :: (OrdA -> OrdA -> OrdA) -> OrdA -> [OrdA] -> OrdA),
  con "drop" (drop :: Int -> [OrdA] -> [OrdA]),
  con "dropWhile" (dropWhile :: (OrdA -> Bool) -> [OrdA] -> [OrdA]),
  con "span" (span :: (OrdA -> Bool) -> [OrdA] -> ([OrdA], [OrdA])),
  con "unzip" (unzip :: [(OrdA, OrdA)] -> ([OrdA], [OrdA])),
  con "+" ((+) :: Int -> Int -> Int),
  con "[]" ([] :: [OrdA]),
  con "partition" (partition :: (OrdA -> Bool) -> [OrdA] -> ([OrdA], [OrdA])),
  con "fst" (fst :: (OrdA, OrdA) -> OrdA),
  con "take" (take :: Int -> [OrdA] -> [OrdA]) ]
