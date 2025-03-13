-- A simple example testing arithmetic functions.
import QuickSpec
import QuickSpec.Internal
import Test.QuickCheck

ceildiv :: Integer -> Integer -> Integer
ceildiv x y = x `div` y + (if x `mod` y == 0 then 0 else 1)

rounddiv :: Integer -> Integer -> Integer
rounddiv x y = (x `ceildiv` y) * y

main = quickSpec [
  instFun (arbitrary `suchThat` (> 0) :: Gen Integer),
  withConsistencyCheck,
  background [
    con "1" (1 :: Integer),
    con "+" ((+) :: Integer -> Integer -> Integer),
    con "*" ((*) :: Integer -> Integer -> Integer),
    predicate "<=" ((<=) :: Integer -> Integer -> Bool) ],
  series [
    con "rounddiv" rounddiv,
    con "ceildiv" ceildiv ]]
