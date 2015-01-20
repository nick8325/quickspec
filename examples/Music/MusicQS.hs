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
         arbitrary = liftM4 Context arbitrary arbitrary arbitrary arbitrary


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
      -- Step 1
      constant "+" (\(Positive x) (Positive y) -> Positive (x+y) :: Positive Rational),
      constant "+'" ((+) :: Int -> Int -> Int),
      -- constant "max" (\(Positive x) (Positive y) -> Positive (max x y) :: Positive Rational),
      constant "*" (\(Positive x) (Positive y) -> Positive (x*y) :: Positive Rational),
      constant "1" (Positive 1 :: Positive Rational),
      constant "recip" (\(Positive x) -> Positive (1/x) :: Positive Rational),

      -- Step 2
      constant ":+:" (:+:),
      constant ":=:" (:=:),

      -- -- Step 3
      constant "tempo" tempo,
      constant "Trans" Trans,
      constant "Instr" Instr,

      -- Step 4
      constant "note" note,
      constant "rest" rest,

      -- Step 5
      constant "dur" (Positive . dur),

      -- Step 6
      constant "cut" (\(Positive x) m -> cut x m),

      -- Step 7
      constant "/=:" (/=:)
      ]
      --extraPruner = Just (SPASS 1)
    }

--main = quickSpec (addBackground background sig) >>= printTheory
main = incrementalQuickSpec sig

background = [
  "recip(1) = 1",
  "*(X1, 1) = X1",
  "*(1, X1) = X1",
  "recip(recip(X1)) = X1",
  "+(1, X1) = +(X1, 1)",
  "+'(X1, X2) = +'(X2, X1)",
  "+(X1, X2) = +(X2, X1)",
  "*(X1, X2) = *(X2, X1)",
  "*(X1, recip(X1)) = 1",
  "*(*(X1, X2), X3) = *(X1, *(X2, X3))",
  "+(+(X1, X2), X3) = +(X1, +(X2, X3))",
  "+'(+'(X1, X2), X3) = +'(X1, +'(X2, X3))",
  "*(X1, +(X2, 1)) = +(X1, *(X1, X2))",
  "*(X1, +(X2, X2)) = *(X2, +(X1, X1))",
  "+(1, *(X1, recip(X2))) = *(+(X2, X1), recip(X2))",
  "+(*(X1, X2), *(X1, X3)) = *(X1, +(X2, X3))",
  ":=:(X1, X2) = :=:(X2, X1)",
  ":+:(:+:(X1, X2), X3) = :+:(X1, :+:(X2, X3))",
  ":=:(:=:(X1, X2), X3) = :=:(X1, :=:(X2, X3))",
  ":=:(:+:(:=:(X1, X1), X2), X1) = :=:(X1, :=:(X1, :+:(X1, X2)))",
  "tempo(1, X1) = X1",
  "Instr(X1, Instr(X2, X3)) = Instr(X2, X3)",
  "Trans(X1, Instr(X2, X3)) = Instr(X2, Trans(X1, X3))",
  "Trans(+'(X1, X2), X3) = Trans(X1, Trans(X2, X3))",
  "tempo(X1, Instr(X2, X3)) = Instr(X2, tempo(X1, X3))",
  "tempo(X1, Trans(X2, X3)) = Trans(X2, tempo(X1, X3))",
  "tempo(*(X1, X2), X3) = tempo(X1, tempo(X2, X3))",
  ":+:(Instr(X1, X2), Instr(X1, X3)) = Instr(X1, :+:(X2, X3))",
  ":+:(Trans(X1, X2), Trans(X1, X3)) = Trans(X1, :+:(X2, X3))",
  ":+:(tempo(X1, X2), tempo(X1, X3)) = tempo(X1, :+:(X2, X3))",
  ":=:(Instr(X1, X2), Instr(X1, X3)) = Instr(X1, :=:(X2, X3))",
  ":=:(Trans(X1, X2), Trans(X1, X3)) = Trans(X1, :=:(X2, X3))",
  ":=:(tempo(X1, X2), tempo(X1, X3)) = tempo(X1, :=:(X2, X3))",
  "tempo(X1, tempo(+(1, 1), X2)) = tempo(+(X1, X1), X2)",
  "Instr(X1, rest(X2)) = rest(X2)",
  "Trans(X1, rest(X2)) = rest(X2)",
  "tempo(X1, rest(X1)) = rest(1)",
  "tempo(X1, note(X2, X1)) = note(X2, 1)",
  ":+:(rest(X1), rest(X2)) = rest(+(X1, X2))",
  ":=:(rest(X1), rest(X1)) = rest(X1)",
  ":=:(note(X1, X2), rest(X2)) = note(X1, X2)",
  "tempo(X1, note(X2, +(X1, X1))) = note(X2, +(1, 1))",
  "tempo(X1, note(X2, +(X1, 1))) = note(X2, +(1, recip(X1)))",
  "note(X1, recip(+(1, recip(X2)))) = tempo(+(X2, 1), note(X1, X2))",
  "dur(rest(X1)) = X1",
  "dur(:=:(X1, X1)) = dur(X1)",
  "dur(Instr(X1, X2)) = dur(X2)",
  "dur(Trans(X1, X2)) = dur(X2)",
  "dur(note(X1, X2)) = X2",
  "dur(:+:(X1, X2)) = dur(:+:(X2, X1))",
  "*(dur(X1), recip(X2)) = dur(tempo(X2, X1))",
  "+(dur(X1), dur(X2)) = dur(:+:(X1, X2))",
  ":=:(X1, rest(dur(X1))) = X1",
  "rest(dur(tempo(X1, X2))) = tempo(X1, rest(dur(X2)))",
  "tempo(X1, note(X2, dur(X3))) = note(X2, dur(tempo(X1, X3)))",
  "dur(:=:(X1, :+:(X1, X2))) = dur(:+:(X1, X2))",
  "dur(:=:(X1, :+:(X2, X1))) = dur(:+:(X1, X2))",
  "dur(:=:(X1, :=:(X1, X2))) = dur(:=:(X1, X2))",
  "dur(:=:(X1, Trans(X2, X3))) = dur(:=:(X1, X3))",
  "dur(:=:(X1, note(X2, X3))) = dur(:=:(X1, rest(X3)))",
  "dur(:=:(X1, rest(dur(X2)))) = dur(:=:(X1, X2))",
  "rest(dur(:=:(X1, rest(recip(X2))))) = rest(dur(X1))",
  "cut(X1, rest(X1)) = rest(X1)",
  "cut(dur(X1), X1) = X1",
  "cut(X1, :+:(rest(X1), X2)) = rest(X1)",
  "cut(dur(X1), :+:(X1, X2)) = X1"]


-- Weird bugs:
-- Why do we get
--   ((m :=: m) :+: m2) :=: m = m :=: (m :=: (m :+: m2))
-- and not
--   (m :=: m) :+: m2 = m :=: (m :+: m2)?
-- Why don't we get
--   Rest x :=: Rest y = Rest (max x y)?

-- TO DO:
-- Make it so we don't have to use the silly Positive type
