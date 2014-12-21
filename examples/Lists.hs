import QuickSpec

sig =
  signature {
    constants = [
      constant "reverse" (reverse :: [A] -> [A]),
      constant "sum" (sum :: [Int] -> Int),
      constant "++" ((++) :: [A] -> [A] -> [A]),
      constant "[]" ([] :: [A]),
      constant "map" (map :: (A -> B) -> [A] -> [B]),
      constant "length" (length :: [A] -> Int),
      constant "concat" (concat :: [[A]] -> [A]) ]}

main = quickSpec sig
