{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable #-}
--module MusicQS where 

import Music hiding (main)
import Perform
import Test.QuickCheck
import Data.Ratio
import Control.Monad
import QuickSpec
import Data.Monoid

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

data Mp = Mp {x :: Music, y :: Music}

arb = do
        m <- arbitrary
        n <- arbitrary
        if dur m < dur n then
            return $ Mp n (m :+: Rest (dur n - dur m))
        else
            return $ Mp m (n :+: Rest (dur m - dur n))

instance Arbitrary Context where
         shrink = genericShrink
         arbitrary = liftM4 Context arbitrary arbitrary (arbitrary `suchThat` (> 0)) arbitrary


note :: (PitchClass, Int) -> Positive Rational -> Music
note n (Positive x) = Note n x

rest :: Positive Rational -> Music
rest (Positive x) = Rest x

tempo :: Positive Rational -> Music -> Music
tempo (Positive x) m = Tempo x m

obsMusic :: Context -> Music -> Performance
obsMusic ctx m = perform ctx (m :+: c 1 tn)

prop_com :: Context -> Music -> Music -> Property
prop_com c m1 m2 = perform c (m1 :=: m2) === perform c (m2 :=: m1)

prop_rest :: Context -> Positive Rational -> Positive Rational -> Property
prop_rest c (Positive x) (Positive y) = perform c ((Rest x :=: Rest y) :+: Note (C, 1) 1) === perform c (Rest (max x y) :+: Note (C, 1) 1)

prop_assoc :: Context -> Music -> Music -> Music -> Property
prop_assoc c m1 m2 m3 = perform c ((m1 :+: m2) :+: m3) === perform c (m1 :+: (m2 :+: m3))

main = quickSpec [
  inst (observe arbitrary obsMusic),
  inst (Sub Dict :: () :- Arbitrary Music),
  baseTypeNames ["i"] (Proxy :: Proxy IName),
  baseTypeNames ["p"] (Proxy :: Proxy PitchClass),
  baseType (Proxy :: Proxy Rational),
  baseType (Proxy :: Proxy (Positive Rational)),
  inst (Names ["m"] :: Names Music),
  inst (Names ["p"] :: Names Mp),

  series [bg, sig1, sig2, sig3, sig4, sig5, sig6] ]
  where
    bg = [
      con "x" x,
      con "y" y,
      con "+" (\(Positive x) (Positive y) -> Positive (x+y) :: Positive Rational),
      con "+'" ((+) :: Int -> Int -> Int),
      con "max" (\(Positive x) (Positive y) -> Positive (max x y) :: Positive Rational),
      con "*" (\(Positive x) (Positive y) -> Positive (x*y) :: Positive Rational),
      con "1" (Positive 1 :: Positive Rational),
      con "recip" (\(Positive x) -> Positive (1/x) :: Positive Rational) ]

    sig1 = [
      con ":+:" (:+:),
      con ":=:" (:=:) ]

    sig2 = [
      con "tempo" tempo,
      con "Trans" Trans,
      con "Instr" Instr ]

    sig3 = [
      con "note" note,
      con "rest" rest ]

    sig4 = [
      con "dur" (Positive . dur) ]

    sig5 = [
      con "cut" (\(Positive x) m -> cut x m) ]

    sig6 = [
      con "/=:" (/=:) ]
