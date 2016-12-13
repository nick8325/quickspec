import Control.Monad
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
                  predicateGen "eqLen"
                  ((\xs ys -> length xs == length ys) :: [Int] -> [Int] -> Bool) eqLenGen]
   }

eqLenGen :: Gen [Dynamic]
eqLenGen = do
  len <- arbitrary
  xs1 <- (replicateM len arbitrary :: Gen [Int])
  xs2 <- (replicateM len arbitrary :: Gen [Int])
  return [toDyn xs1, toDyn xs2]

main = quickSpec sig
