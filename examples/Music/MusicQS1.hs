{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable #-}
--module MusicQS where 

import Music hiding (main)
import Perform
import Test.QuickCheck
import Data.Ratio
import Control.Monad
import Test.QuickSpec
import Data.Typeable

deriving instance Typeable Positive

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
                arb' 0 = oneof [liftM2 note arbitrary arbitrary,
                               liftM rest arbitrary]
                arb' n = oneof [liftM2 note arbitrary arbitrary,
                               liftM rest arbitrary,
                               liftM2 (:+:) submusic2 submusic2,
                               liftM2 (:=:) submusic2 submusic2,
                               liftM2 tempo arbitrary submusic,
                               liftM2 Trans arbitrary submusic,
                               liftM2 Instr arbitrary submusic]
                       where submusic = arb' (n-1)
                             submusic2 = arb' (n `div` 2)

instance Arbitrary Context where
         shrink = genericShrink
         arbitrary = liftM4 Context arbitrary arbitrary (arbitrary `suchThat` (> 0)) arbitrary


note :: (PitchClass, Int) -> Positive Rational -> Music
note n (Positive x) = Note n x

rest :: Positive Rational -> Music
rest (Positive x) = Rest x

tempo :: Positive Rational -> Music -> Music
tempo (Positive x) m = Tempo x m

obsMusic :: Music -> Gen Performance
obsMusic m = liftM2 perform arbitrary (return (m :+: c 1 tn)) 

prop_com :: Context -> Music -> Music -> Property
prop_com c m1 m2 = perform c (m1 :=: m2) === perform c (m2 :=: m1)

prop_assoc :: Context -> Music -> Music -> Music -> Property
prop_assoc c m1 m2 m3 = perform c ((m1 :+: m2) :+: m3) === perform c (m1 :+: (m2 :+: m3))

sig =
  signature [
    observer2 (\ctx x -> perform ctx (x :+: c 1 tn)),
    vars ["x", "y", "z"] (undefined :: (PitchClass, Int)),
    vars ["x", "y", "z"] (undefined :: IName),
    vars ["x", "y", "z"] (undefined :: Music),
    vars ["x", "y", "z"] (undefined :: Positive Rational),
    vars ["x", "y", "z"] (undefined :: Int),
    fun2 "+" (\(Positive x) (Positive y) -> Positive (x+y) :: Positive Rational),
    fun2 "max" (\(Positive x) (Positive y) -> Positive (max x y) :: Positive Rational),
    fun2 "+'" ((+) :: Int -> Int -> Int),
    fun2 "*" (\(Positive x) (Positive y) -> Positive (x*y) :: Positive Rational),
    fun0 "1" (Positive 1 :: Positive Rational),
    fun1 "recip" (\(Positive x) -> Positive (1/x) :: Positive Rational),
    blind2 ":+:" (:+:),
    blind2 ":=:" (:=:),
    blind2 "tempo" tempo,
    blind2 "Trans" Trans,
    blind2 "Instr" Instr,
    blind2 "note" note,
    blind1 "rest" rest,
    fun1 "dur" (Positive . dur),
    blind2 "cut" (\(Positive x) m -> cut x m),
    blind2 "/=:" (/=:) ]

main = quickSpec sig
