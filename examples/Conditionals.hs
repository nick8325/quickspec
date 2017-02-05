{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import Data.Dynamic
import GHC.TypeLits

sig =
  signature {
    maxTermSize = Just 8,
    --maxTests    = Just 10000,
    constants = [
       --constant "[]" ([] :: [Int]),
       --constant ":"  ((:) :: Int -> [Int] -> [Int]),
       constant "++" ((++) :: [A] -> [A] -> [A]),
       --constant "head" (head :: [A] -> A),
       constant "zip" (zip :: [A] -> [A] -> [(A,A)])
       --constant "length" (length :: [A] -> Int),
       --constant "reverse" (reverse :: [A] -> [A])
    ],
    predicates = [--predicate (undefined :: Proxy "notNull") ((not . null) :: [Int] -> Bool),
                  predicate (undefined :: Proxy "eqLen")
                  ((\xs ys -> length xs == length ys) :: [A] -> [A] -> Bool)]
   }

main = quickSpec sig
