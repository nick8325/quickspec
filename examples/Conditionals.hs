-- A test for conditions.
-- Many laws for zip only hold when the arguments have the same
-- length.
import QuickSpec

sig =
  signature {
    maxTermSize = Just 8,
    constants = [
       constant "++" ((++) :: [Int] -> [Int] -> [Int]),
       constant "zip" (zip :: [Int] -> [Int] -> [(Int,Int)])
    ],
    predicates = [ predicate "eqLen"
                  ((\xs ys -> length xs == length ys) :: [Int] -> [Int] -> Bool)
                 ]
   }

main = quickSpec sig
