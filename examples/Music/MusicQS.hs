{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable #-}
--module MusicQS where 

import Music hiding (main)
import Perform
import Test.QuickCheck
import Data.Ratio
import Control.Monad
import QuickSpec hiding ((:=:), background)

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
                dur = arbitrary `suchThat` (>= 0)
                arb' 0 = oneof [liftM2 Note arbitrary dur,
                               liftM Rest dur]
                arb' n = oneof [liftM2 Note arbitrary dur,
                               liftM Rest dur,
                               liftM2 (:+:) submusic2 submusic2,
                               liftM2 (:=:) submusic2 submusic2,
                               liftM2 tempo arbitrary submusic,
                               liftM2 Trans arbitrary submusic,
                               liftM2 Instr arbitrary submusic]
                       where submusic = arb' (n-1)
                             submusic2 = arb' (n `div` 2)

instance Arbitrary Context where
         shrink = genericShrink
         arbitrary = liftM4 Context arbitrary arbitrary arbitrary arbitrary


tempo :: Positive Rational -> Music -> Music
tempo (Positive x) m = Tempo x m

obsMusic :: Music -> Gen Performance
obsMusic m = liftM2 perform arbitrary (return (m :+: c 1 tn)) 

prop_com :: Context -> Music -> Music -> Property
prop_com c m1 m2 = perform c (m1 :=: m2) === perform c (m2 :=: m1)

prop_assoc :: Context -> Music -> Music -> Music -> Property
prop_assoc c m1 m2 m3 = perform c ((m1 :+: m2) :+: m3) === perform c (m1 :+: (m2 :+: m3))
sig =
  signature {
    maxTermSize = Just 7,
    instances = [
      makeInstance (\() -> observe obsMusic),
      inst (Sub Dict :: () :- Arbitrary Music),
      baseTypeNames ["i"] (undefined :: IName),
      baseTypeNames ["p"] (undefined :: PitchClass),
      baseType (undefined :: Rational),
      baseType (undefined :: Positive Rational),
      names (NamesFor ["m"] :: NamesFor Music)
      ],
    constants = [
      constant "*" (\(Positive x) (Positive y) -> Positive (x*y) :: Positive Rational),
      constant "*'" (\(Positive x) y -> x*y :: Rational),
      constant "1" (Positive 1 :: Positive Rational),
      constant "1'" (1 :: Rational),
      constant "recip" (\(Positive x) -> Positive (1/x) :: Positive Rational),
      constant "note" Note,
      constant "rest" Rest,
      constant ":+:" (:+:),
      constant ":=:" (:=:),
      constant "tempo" tempo
      --constant "Trans" Trans,
      --constant "Instr" Instr
      ],
      extraPruner = Just (SPASS 1)
    }

background = [
  "recip(1) = 1",
  "*(X1, 1) = X1",
  "*(1, X1) = X1",
  "*'(1, X1) = X1",
  "recip(recip(X1)) = X1",
  ":=:(X1, X2) = :=:(X2, X1)",
  "*(X1, X2) = *(X2, X1)",
  "*(X1, recip(X1)) = 1",
  "*(*(X1, X2), X3) = *(X1, *(X2, X3))",
  "*'(*(X1, X2), X3) = *'(X1, *'(X2, X3))",
  ":+:(:+:(X1, X2), X3) = :+:(X1, :+:(X2, X3))",
  ":=:(:=:(X1, X2), X3) = :=:(X1, :=:(X2, X3))",
  ":=:(rest(X1), rest(X1)) = rest(X1)",
  ":+:(rest(1'), rest(X1)) = :+:(rest(X1), rest(1'))",
  ":+:(rest(X1), rest(X2)) = :+:(rest(X2), rest(X1))",
  ":=:(note(X1, X2), rest(X2)) = note(X1, X2)",
  ":=:(:+:(:=:(X1, X1), X2), X1) = :=:(X1, :=:(X1, :+:(X1, X2)))"]

main = quickSpec (addBackground background sig)
