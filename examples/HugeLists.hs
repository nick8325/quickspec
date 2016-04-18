{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds, FlexibleContexts #-}
import QuickSpec
import Data.List
import System.Environment
import Control.Monad

main = do
  args <- getArgs
  case args of
    [] -> quickSpec sig
    [xs] -> quickSpec sig { constants = take (read xs) (constants sig) }
    [xs, ys] -> quickSpec sig { constants = take (read xs) (constants sig), maxTermSize = Just (read ys) }

sig =
  signature {
    printStatistics = True,
    maxTermSize = Just 7,
    constants = [
      constant "length" (length :: [A] -> Int),
      constant "sort" (sort :: [Int] -> [Int]),
      constant "scanr" (scanr :: (A -> B -> B) -> B -> [A] -> [B]),
      constant "succ" (succ :: Int -> Int),
      constant ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B]),
      constant "snd" (snd :: (A, B) -> B),
      constant "reverse" (reverse :: [A] -> [A]),
      constant "id" (id :: ([A], [B]) -> ([A], [B])),
      constant "0" (0 :: Int),
      constant "," ((,) :: A -> B -> (A, B)),
      constant ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C]),
      constant ":" ((:) :: A -> [A] -> [A]),
      constant "break" (break :: (A -> Bool) -> [A] -> ([A], [A])),
      constant "filter" (filter :: (A -> Bool) -> [A] -> [A]),
      constant "scanl" (scanl :: (B -> A -> B) -> B -> [A] -> [B]),
      constant "zipWith" (zipWith :: (A -> B -> C) -> [A] -> [B] -> [C]),
      constant "concat" (concat :: [[A]] -> [A]),
      constant "zip" (zip :: [A] -> [B] -> [(A, B)]),
      constant "usort" (usort :: [Int] -> [Int]),
      constant "sum" (sum :: [Int] -> Int),
      constant "++" ((++) :: [A] -> [A] -> [A]),
      constant "map" (map :: (A -> B) -> [A] -> [B]),
      constant "foldl" (foldl :: (B -> A -> B) -> B -> [A] -> B),
      constant "takeWhile" (takeWhile :: (A -> Bool) -> [A] -> [A]),
      constant "foldr" (foldr :: (A -> B -> B) -> B -> [A] -> B),
      constant "drop" (drop :: Int -> [A] -> [A]),
      constant "dropWhile" (dropWhile :: (A -> Bool) -> [A] -> [A]),
      constant "span" (span :: (A -> Bool) -> [A] -> ([A], [A])),
      constant "unzip" (unzip :: [(A, B)] -> ([A], [B])),
      constant "+" ((+) :: Int -> Int -> Int),
      constant "[]" ([] :: [A]),
      constant "partition" (partition :: (A -> Bool) -> [A] -> ([A], [A])),
      constant "fst" (fst :: (A, B) -> A),
      constant "take" (take :: Int -> [A] -> [A]) ]}
