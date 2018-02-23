-- Sorting and sorted lists.
-- Illustrates testing of conditional laws.
import QuickSpec
import Data.List

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted [_] = True
sorted (x:y:xs) = x <= y && sorted (y:xs)

main = quickSpec [
  background [
    con ":" ((:) :: A -> [A] -> [A]),
    con "[]" ([] :: [A]) ],

  con "sort" (sort :: [Int] -> [Int]),
  con "insert" (insert :: Int -> [Int] -> [Int]),
  predicate "sorted" (sorted :: [Int] -> Bool) ]
