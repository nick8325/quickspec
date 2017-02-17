{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import Data.Dynamic
import GHC.TypeLits
import QuickSpec.Signature

sig =
  signature {
    maxTermSize = Just 8,
    --maxTests    = Just 10000,
    constants = [
       --constant "[]" ([] :: [Int]),
       --constant ":"  ((:) :: Int -> [Int] -> [Int]),
       constant "++" ((++) :: [A] -> [A] -> [A]),
       --constant "head" (head :: [A] -> A),
       constant "zip" (zip :: [Int] -> [Int] -> [(Int,Int)])
       --constant "length" (length :: [A] -> Int),
       --constant "reverse" (reverse :: [A] -> [A])
    ],
    predicates = [--predicate (undefined :: Proxy "notNull") ((not . null) :: [Int] -> Bool),
                  predicate (undefined :: Proxy "eqLen")
                  ((\xs ys -> length xs == length ys) :: [Int] -> [Int] -> Bool)]
   }

main = quickSpec sig --mapM_ print (instances_ (predicateSig sig))
  
--quickSpec sig
