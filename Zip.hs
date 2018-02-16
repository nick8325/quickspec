import QuickSpec

main = quickSpec [
  withMaxTermSize 8,
  constant "zip" (zip :: [A] -> [B] -> [(A,B)]),
  constant "++" ((++) :: [A] -> [A] -> [A]),
  predicate "eqLen" ((\xs ys -> length xs == length ys) :: [A] -> [A] -> Bool) ]
  --constant "map_fst" (map fst :: [(A, B)] -> [A])]
  --constant "map" (map :: (A -> B) -> [A] -> [B]),
  --constant "fst" (fst :: (A, B) -> A) ]
