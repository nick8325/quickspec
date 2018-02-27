{-# LANGUAGE FlexibleContexts, RankNTypes, ConstraintKinds #-}
-- Sorting and sorted lists.
-- Illustrates testing of conditional laws.
import QuickSpec
import Data.List

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted [_] = True
sorted (x:y:xs) = x <= y && sorted (y:xs)

lift :: (c => a) -> Dict c -> a
lift f Dict = f

main = quickSpec [
  con "[]" ([] :: [A]),
  con ":" ((:) :: A -> [A] -> [A]),
  con "sort" (lift sort :: Dict (Ord A) -> [A] -> [A]),
  con "insert" (lift insert :: Dict (Ord A) -> A -> [A] -> [A]),
  predicate "sorted" (lift sorted :: Dict (Ord A) -> [A] -> Bool) ]
