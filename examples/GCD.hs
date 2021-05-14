-- A simple example testing arithmetic functions.
import QuickSpec
import Numeric.Natural

main = quickSpec [
  series [
    [con "0" (0 :: Natural),
     con "1" (1 :: Natural),
     con "+" ((+) :: Natural -> Natural -> Natural),
     con "*" ((*) :: Natural -> Natural -> Natural)],
    [con "gcd" (gcd :: Natural -> Natural -> Natural)]]]
