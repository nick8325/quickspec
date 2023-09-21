-- A simple example testing arithmetic functions.
import QuickSpec

main = quickSpec [
    con "0" (0 :: Float)
  , con "1" (1 :: Float)
  , con "+" ((+) :: Float -> Float -> Float)
  , con "*" ((*) :: Float -> Float -> Float)
  , monoType (Proxy :: Proxy Float)
  , withConsistencyCheck
  ]
