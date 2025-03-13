-- A simple example testing arithmetic functions.
import QuickSpec
import QuickSpec.Internal
import Test.QuickCheck

main = quickSpec [
  monoType (Proxy :: Proxy Float),
  withMaxTests 10000,
  withConsistencyCheck,

  con "0" (0 :: Float),
  con "1" (1 :: Float),
  con "+" ((+) :: Float -> Float -> Float),
  con "*" ((*) :: Float -> Float -> Float),
  con "/" ((/) :: Float -> Float -> Float) ]
