{-# LANGUAGE DeriveDataTypeable #-}
import QuickSpec
import Test.QuickCheck

data Table9Point1 = I | A | B | C | D deriving (Eq, Ord, Show, Typeable)

instance Arbitrary Table9Point1 where
  arbitrary = elements [I, A, B, C, D]

instance CoArbitrary Table9Point1 where
  coarbitrary = coarbitraryShow

times :: Table9Point1 -> Table9Point1 -> Table9Point1
times I I = I
times I A = A
times I B = B
times I C = C
times I D = D
times A I = A
times A A = A
times A B = B
times A C = D
times A D = D
times B I = B
times B A = B
times B B = D
times B C = A
times B D = A
times C I = C
times C A = D
times C B = A
times C C = B
times C D = B
times D I = D
times D A = D
times D B = A
times D C = B
times D D = B

sig =
  signature {
      constants = [
        constant "times" times,
        constant "i" I,
        constant "a" A,
        constant "b" B,
        constant "c" C,
        constant "d" D ],
      instances = [
        baseType (undefined :: Table9Point1)]}

main = quickSpec sig
