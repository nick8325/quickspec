import Data.Proxy
import Data.List
import QuickSpec

sorted :: Ord a => [a] -> Bool
sorted xs = sort xs == xs

insert' :: Ord a => a -> [a] -> [a]
insert' x xs = if sorted xs then insert x xs else insert x (reverse xs)

main = quickSpec [
  constant "insert" (insert' :: Int -> [Int] -> [Int]),
  constant "sort" (sort :: [Int] -> [Int]),
  constant ":" ((:) :: Int -> [Int] -> [Int]),
  predicate "sorted" (sorted :: [Int] -> Bool) ]
  
  -- --constant "[]" ([] :: [A]),
  -- --constant "[]'" ([] :: [Int]),
  -- constant "+" ((+) :: Int -> Int -> Int),
  -- constant "length" (length :: [A] -> Int),
  -- constant "++" ((++) :: [A] -> [A] -> [A])]
  -- --constant "blah" ([1] :: [Int]),
  -- --constant "1" (1 :: Int),
