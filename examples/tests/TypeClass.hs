-- A simple example testing arithmetic functions.
{-# LANGUAGE TypeOperators
           , TypeApplications
#-}
import QuickSpec

-- Integers
main = quickSpec [ con "0" (liftC 0   :: Num A ==> A)
                 , con "1" (liftC 1   :: Num A ==> A)
                 , con "+" (liftC (+) :: Num A ==> (A -> A -> A))
                 , con "*" (liftC (*) :: Num A ==> (A -> A -> A))
                 , instanceOf @(Num Float)
                 , monoType (Proxy :: Proxy Float)
                 ]
