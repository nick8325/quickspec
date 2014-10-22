import QuickSpec

sig =
  signature {
    constants = [
       constant "0" (0 :: Int),
       constant "1" (1 :: Int),
       constant "+" ((+) :: Int -> Int -> Int),
       constant "*" ((*) :: Int -> Int -> Int) ]}

main = quickSpec sig
