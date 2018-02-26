{-# LANGUAGE GADTs
           , TypeOperators
           , ConstraintKinds
           , RankNTypes
           , TypeApplications
#-}
-- A simple example testing arithmetic functions.
import QuickSpec

data Instance c where
  Instance :: c => Instance c

type c ==> t = Instance c -> t

lift :: (c => t) -> c ==> t
lift f Instance = f

-- Integers
main0 = quickSpec [ withMaxTermSize 10 
                  , con "0" (lift 0 :: Num A ==> A)
                  , con "1" (lift 1 :: Num A ==> A)
                  , con "+" (lift (+) :: Num A ==> (A -> A -> A))
                  , con "*" (lift (*) :: Num A ==> (A -> A -> A))
                  , con ""  (Instance @(Num Int))
                  ]

-- Functors
main1 = quickSpec [ withMaxTermSize 10
                  , con "fmap" (lift fmap :: Functor F ==> ( (A -> B) -> (F A -> F B) ))
                  , con "id"   (id :: A -> A)
                  , con "" (Instance @(Functor []))
                  , con "" (Instance @(Functor Maybe))
                  ]
