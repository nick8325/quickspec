-- A simple example testing arithmetic functions.
{-# LANGUAGE TypeOperators
           , TypeApplications
#-}
import QuickSpec

-- Integers
main0 = quickSpec [ withMaxTermSize 7
                  , con "0" (liftC 0 :: Num A ==> A)
                  , con "1" (liftC 1 :: Num A ==> A)
                  , con "+" (liftC (+) :: Num A ==> (A -> A -> A))
                  , con "*" (liftC (*) :: Num A ==> (A -> A -> A))
                  , instanceOf @(Num Int)
                  ]

-- Functors
main1 = quickSpec [ withMaxTermSize 10
                  , con "fmap" (liftC fmap :: Functor F ==> ( (A -> B) -> (F A -> F B) ))
                  , con "id"   (id :: A -> A)
                  , instanceOf @(Functor [])
                  ]
