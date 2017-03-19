{-# LANGUAGE DataKinds #-}
import QuickSpec
import GHC.TypeLits

sig =
  signature {
    maxTermSize = Just 8,
    constants = [
       constant "++" ((++) :: [Int] -> [Int] -> [Int]),
       constant "zip" (zip :: [Int] -> [Int] -> [(Int,Int)])
    ],
    predicates = [ predicate (undefined :: Proxy "eqLen")
                  ((\xs ys -> length xs == length ys) :: [Int] -> [Int] -> Bool)
                 ]
   }

main = quickSpec sig
