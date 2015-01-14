{-# LANGUAGE TypeOperators #-}
--module MusicQS where 

import Music hiding (main)
import Perform
import Test.QuickCheck
import Data.Ratio
import Control.Monad
import QuickSpec hiding ((:=:))


instance Arbitrary IName where
         arbitrary = oneof (map return [AcousticGrandPiano .. Percussion])
         shrink = genericShrink

instance Arbitrary PitchClass where
         arbitrary = oneof (map return [Cf .. Bs])
         shrink = genericShrink

instance Arbitrary Music where
         shrink = genericShrink
         arbitrary = sized arb' 
           where
                dur = arbitrary `suchThat` (>= 0)
                arb' 0 = oneof [liftM2 Note arbitrary dur,
                               liftM Rest dur]
                arb' n = oneof [liftM2 Note arbitrary dur,
                               liftM Rest dur,
                               liftM2 (:+:) submusic2 submusic2,
                               liftM2 (:=:) submusic2 submusic2,
                               liftM2 Tempo (arbitrary `suchThat` (>0)) submusic,
                               liftM2 Trans arbitrary submusic,
                               liftM2 Instr arbitrary submusic]
                       where submusic = arb' (n-1)
                             submusic2 = arb' (n `div` 2)

instance Arbitrary Context where
         shrink = genericShrink
         arbitrary = liftM4 Context arbitrary arbitrary arbitrary arbitrary
        
obsMusic :: Music -> Gen Performance
obsMusic m = liftM2 perform arbitrary (return (m :+: c 1 tn)) 

prop_com :: Context -> Music -> Music -> Property
prop_com c m1 m2 = perform c (m1 :=: m2) === perform c (m2 :=: m1)

prop_assoc :: Context -> Music -> Music -> Music -> Property
prop_assoc c m1 m2 m3 = perform c ((m1 :+: m2) :+: m3) === perform c (m1 :+: (m2 :+: m3))
sig = 
    signature {
      maxTermSize = Just 9,
      constants = [
        constant "Note" Note, 
        constant "Rest" Rest,
        constant ":+:" (:+:),
        constant ":=:" (:=:),
        --constant "Tempo" Tempo,
        constant "Trans" Trans,
        constant "Instr" Instr
      ],
      instances = [
        makeInstance (\() -> observe obsMusic),
        inst (Sub Dict :: () :- Arbitrary Music),
        baseTypeNames ["i"] (undefined :: IName),
        baseTypeNames ["p"] (undefined :: PitchClass),
        baseType (undefined :: Ratio Int),
        names (NamesFor ["m"] :: NamesFor Music)
        ]
       --extraPruner = Just (QuickSpec.E 1) 
 
    }

main = quickSpec sig