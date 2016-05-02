{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
import Data.Ratio
import QuickSpec
import Test.QuickCheck
import Twee.Pretty
import Control.Monad

class Fractional a => Conj a where
  conj :: a -> a
  norm :: a -> Rational
  it :: Gen a

instance Conj Rational where
  conj x = x
  norm x = x*x
  it = liftM2 (Prelude./) (elements [-10..10]) (elements [1..10])

instance Conj a => Conj (a, a) where
  conj (x, y) = (conj x, negate y)
  norm (x, y) = norm x + norm y
  it = liftM2 (,) it it

instance Conj a => Num (a, a) where
  fromInteger n = (fromInteger n, 0)
  (x, y) + (z, w) = (x + z, y + w)
  (a, b) * (c, d) = (a * c - conj d * b, d * a + b * conj c)
  negate (x, y) = (negate x, negate y)

instance Conj a => Fractional (a, a) where
  fromRational x = (fromRational x, 0)
  recip x = conj x * fromRational (recip (norm x))

newtype Complex = Complex (Rational, Rational) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)
newtype Quaternion = Quaternion (Complex, Complex) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)
newtype Octonion = Octonion (Quaternion, Quaternion) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)

type It = Octonion

sig =
  signature {
    constants = [
      constant "*" ((*) :: It -> It -> It),
      (constant "^-1" (recip :: It -> It)) { conStyle = postfix },
      constant "1" (1 :: It)
    ],
    maxTermSize = Just 7,
    maxPruningSize = Just 9,
    maxTests = Just 1,
    --extraPruner = Just (Waldmeister 5),
    instances = [
      baseType (undefined :: It),
      makeInstance (\() -> arbitrary `suchThat` (/= 0) :: Gen It)]}

main = quickSpec sig
