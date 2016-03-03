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
    maxTermSize = Just 9,
    constants = [
      constant "[]" ([] :: [A]),
      constant "0" (0 :: Int),
      constant "+" ((+) :: Int -> Int -> Int),
      constant "," ((,) :: A -> B -> (A, B)),
      constant ":" ((:) :: A -> [A] -> [A]),
      constant "fst" (fst :: (A, B) -> A),
      constant "snd" (snd :: (A, B) -> B),
      constant "id" (id :: ([A], [B]) -> ([A], [B])),
      constant "succ" (succ :: Int -> Int),
      constant "++" ((++) :: [A] -> [A] -> [A]),
      constant "concat" (concat :: [[A]] -> [A]),
      constant "head" (head :: [A] -> A),
      constant "return" (return :: A -> [A]),
      constant "map" (map :: (A -> B) -> [A] -> [B]),
      constant "reverse" (reverse :: [A] -> [A]),
      constant "tail" (tail :: [A] -> [A]),
      constant "drop" (drop :: Int -> [A] -> [A]),
      constant "length" (length :: [A] -> Int),
      constant "sum" (sum :: [Int] -> Int),
      constant "take" (take :: Int -> [A] -> [A]),
      constant "span" (span :: (A -> Bool) -> [A] -> ([A], [A])),
      constant "takeWhile" (takeWhile :: (A -> Bool) -> [A] -> [A]),
      constant "break" (break :: (A -> Bool) -> [A] -> ([A], [A])),
      constant "dropWhile" (dropWhile :: (A -> Bool) -> [A] -> [A]),
      constant "filter" (filter :: (A -> Bool) -> [A] -> [A]),
      constant "partition" (partition :: (A -> Bool) -> [A] -> ([A], [A])),
      constant "foldl" (foldl :: (B -> A -> B) -> B -> [A] -> B),
      constant "foldr" (foldr :: (A -> B -> B) -> B -> [A] -> B),
      constant "scanl" (scanl :: (B -> A -> B) -> B -> [A] -> [B]),
      constant "scanr" (scanr :: (A -> B -> B) -> B -> [A] -> [B]),
      constant "unzip" (unzip :: [(A, B)] -> ([A], [B])),
      constant "zip" (zip :: [A] -> [B] -> [(A, B)]),
      constant "zipWith" (zipWith :: (A -> B -> C) -> [A] -> [B] -> [C]),
      constant ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C]),
      constant ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B]),
      constant "sort" (sort :: [Int] -> [Int]),
      constant "usort" (usort :: [Int] -> [Int])]}
