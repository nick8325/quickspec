-- Testing that discovered conditional laws can be given as background theory.
import QuickSpec
import QuickSpec.Internal
import Twee.Pretty
import Data.List

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted [_] = True
sorted (x:y:xs) = x <= y && sorted (y:xs)

sig = signature [
  lists `without` ["++"],
  con "sort" (sort :: [Int] -> [Int]),
  con "insert" (insert :: Int -> [Int] -> [Int]),
  predicate "sorted" (sorted :: [Int] -> Bool) ]

main = do
  thy <- quickSpecResult sig
  quickSpec (sig `mappend` addBackground thy)
