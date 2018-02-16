import QuickSpec

main = quickSpec [
  withMaxTermSize 8,
  withPruningDepth 10,
  constant "zip" (zip :: [Int] -> [Int] -> [(Int,Int)]),
  constant "++" ((++) :: [Int] -> [Int] -> [Int]),
  predicate "eqLen" ((\xs ys -> length xs == length ys) :: [Int] -> [Int] -> Bool) ]
  --constant "map_fst" (map fst :: [(A, B)] -> [A])]
  --constant "map" (map :: (A -> B) -> [A] -> [B]),
  --constant "fst" (fst :: (A, B) -> A) ]
