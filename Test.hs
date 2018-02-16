import Data.Proxy
import QuickSpec

main = quickSpec [
  constant "+" ((+) :: Int -> Int -> Int),
  constant "*" ((*) :: Int -> Int -> Int),
  constant "0" (0 :: Int),
  constant "1" (1 :: Int)]
