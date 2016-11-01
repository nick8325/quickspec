import Test.QuickCheck
import QuickSpec
import Data.Dynamic

sig =
  signature {
    maxTermSize = Just 8,
    constants = [
       constant "[]" ([] :: [Int]),
       constant ":"  ((:) :: Int -> [Int] -> [Int]),
       constant "++" ((++) :: [A] -> [A] -> [A]),
       constant "head" (head :: [A] -> A),
       constant "zip" (zip :: [Int] -> [Int] -> [(Int,Int)]),
       constant "length" (length :: [A] -> Int),
       constant "reverse" (reverse :: [A] -> [A])
    ],
    predicates = [predicate "notNull" ((not . null) :: [Int] -> Bool),
                  predicate "eqLen" ((\xs ys -> length xs == length ys) :: [Int] -> [Int] -> Bool)]
   }

main = quickSpec sig
