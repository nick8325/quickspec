import QuickSpec

main = quickSpec [
  con "0" (0 :: Int),
  con "1" (1 :: Int),
  con "+" ((+) :: Int -> Int -> Int),
  con "*" ((*) :: Int -> Int -> Int) ]
