{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable #-}
--module MusicQS where 

import Music hiding (main)
import Perform
import Test.QuickCheck
import Data.Ratio
import Control.Monad
import QuickSpec hiding ((:=:), background)
import Data.Monoid
import Data.Typeable
import Data.Constraint

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

obsMusic :: Music -> Gen Performance
obsMusic m = liftM2 perform arbitrary (return (m :+: c 1 tn)) 

prop_com :: Context -> Music -> Music -> Property
prop_com c m1 m2 = perform c (m1 :=: m2) === perform c (m2 :=: m1)

prop_rest :: Context -> Positive Rational -> Positive Rational -> Property
prop_rest c (Positive x) (Positive y) = perform c ((Rest x :=: Rest y) :+: Note (C, 1) 1) === perform c (Rest (max x y) :+: Note (C, 1) 1)

prop_assoc :: Context -> Music -> Music -> Music -> Property
prop_assoc c m1 m2 m3 = perform c ((m1 :+: m2) :+: m3) === perform c (m1 :+: (m2 :+: m3))
bg =
  signature {
    maxTermSize = Just 7,
    maxTests = Just 2000,
    instances = [
      makeInstance (\() -> observe obsMusic),
      inst (Sub Dict :: () :- Arbitrary Music),
      baseTypeNames ["i"] (undefined :: IName),
      baseTypeNames ["p"] (undefined :: PitchClass),
      baseType (undefined :: Rational),
      baseType (undefined :: Positive Rational),
      names (NamesFor ["m"] :: NamesFor Music),
      names (NamesFor ["p"] :: NamesFor Mp),
      makeInstance (\() -> arb)
      ],
    constants = [
      constant "x" x,
      constant "y" y,
      constant "+" (\(Positive x) (Positive y) -> Positive (x+y) :: Positive Rational),
      constant "+'" ((+) :: Int -> Int -> Int),
      constant "max" (\(Positive x) (Positive y) -> Positive (max x y) :: Positive Rational),
      constant "*" (\(Positive x) (Positive y) -> Positive (x*y) :: Positive Rational),
      constant "1" (Positive 1 :: Positive Rational),
      constant "recip" (\(Positive x) -> Positive (1/x) :: Positive Rational) ]
    --extraPruner = Just (QuickSpec.E 1)
    }

sig1 =
  signature {
    constants = [
      constant ":+:" (:+:),
      constant ":=:" (:=:) ]}

sig2 =
  signature {
    constants = [
      constant "tempo" tempo,
      constant "Trans" Trans,
      constant "Instr" Instr ]}

sig3 =
  signature {
    constants = [
      constant "note" note,
      constant "rest" rest ]}

sig4 =
  signature {
    constants = [
      constant "dur" (Positive . dur) ]}

sig5 =
  signature {
    constants = [
      constant "cut" (\(Positive x) m -> cut x m) ]}

sig6 =
  signature {
    constants = [
      constant "/=:" (/=:) ]}

main = do
  thy <- quickSpec bg
  thy <- quickSpec (thy `mappend` sig1)
  thy <- quickSpec (thy `mappend` sig2)
  thy <- quickSpec (thy `mappend` sig3)
  thy <- quickSpec (thy `mappend` sig4)
  thy <- quickSpec (thy `mappend` sig5)
  quickSpec (thy `mappend` sig6)

-- Weird bugs:
-- Why do we get
--   ((m :=: m) :+: m2) :=: m = m :=: (m :=: (m :+: m2))
-- and not
--   (m :=: m) :+: m2 = m :=: (m :+: m2)?
-- Why don't we get
--   Rest x :=: Rest y = Rest (max x y)?

-- TO DO:
-- Make it so we don't have to use the silly Positive type
