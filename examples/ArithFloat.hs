-- Shows the use of the 'withConsistencyCheck' function.
-- Here, QuickSpec discovers false laws, but withConsistencyCheck
-- produces a warning for them.

import QuickSpec
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
