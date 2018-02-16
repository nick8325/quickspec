import Data.Proxy
import QuickSpec

main = quickSpec [
  --constant "[]" ([] :: [A]),
  --constant "[]'" ([] :: [Int]),
  constant "+" ((+) :: Int -> Int -> Int),
  constant "length" (length :: [A] -> Int),
  constant "++" ((++) :: [A] -> [A] -> [A])]
  --constant "blah" ([1] :: [Int]),
  --constant "1" (1 :: Int),
