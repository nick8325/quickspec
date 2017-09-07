-- A stress test using lots and lots of list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds, FlexibleContexts #-}
import QuickSpec
import QuickSpec.Utils
import Data.List
import Control.Monad

main = quickSpec [
  con "length" (length :: [A] -> Int),
  con "sort" (sort :: [Int] -> [Int]),
  con "scanr" (scanr :: (A -> B -> B) -> B -> [A] -> [B]),
  con "succ" (succ :: Int -> Int),
  con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B]),
  con "snd" (snd :: (A, B) -> B),
  con "reverse" (reverse :: [A] -> [A]),
  con "id" (id :: ([A], [B]) -> ([A], [B])),
  con "0" (0 :: Int),
  con "," ((,) :: A -> B -> (A, B)),
  con ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C]),
  con ":" ((:) :: A -> [A] -> [A]),
  con "break" (break :: (A -> Bool) -> [A] -> ([A], [A])),
  con "filter" (filter :: (A -> Bool) -> [A] -> [A]),
  con "scanl" (scanl :: (B -> A -> B) -> B -> [A] -> [B]),
  con "zipWith" (zipWith :: (A -> B -> C) -> [A] -> [B] -> [C]),
  con "concat" (concat :: [[A]] -> [A]),
  con "zip" (zip :: [A] -> [B] -> [(A, B)]),
  con "usort" (usort :: [Int] -> [Int]),
  con "sum" (sum :: [Int] -> Int),
  con "++" ((++) :: [A] -> [A] -> [A]),
  con "map" (map :: (A -> B) -> [A] -> [B]),
  con "foldl" (foldl :: (B -> A -> B) -> B -> [A] -> B),
  con "takeWhile" (takeWhile :: (A -> Bool) -> [A] -> [A]),
  con "foldr" (foldr :: (A -> B -> B) -> B -> [A] -> B),
  con "drop" (drop :: Int -> [A] -> [A]),
  con "dropWhile" (dropWhile :: (A -> Bool) -> [A] -> [A]),
  con "span" (span :: (A -> Bool) -> [A] -> ([A], [A])),
  con "unzip" (unzip :: [(A, B)] -> ([A], [B])),
  con "+" ((+) :: Int -> Int -> Int),
  con "[]" ([] :: [A]),
  con "partition" (partition :: (A -> Bool) -> [A] -> ([A], [A])),
  con "fst" (fst :: (A, B) -> A),
  con "take" (take :: Int -> [A] -> [A]) ]
