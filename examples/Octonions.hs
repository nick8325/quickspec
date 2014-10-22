{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances, TypeOperators #-}
import Prelude hiding ((/))
import qualified Prelude
import Data.Ratio
import Control.Monad
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Data.Ord
import QuickSpec hiding (compose, (\\))

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

newtype Complex = Complex (Rational, Rational) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary)
newtype Quaternion = Quaternion (Complex, Complex) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary)
newtype Octonion = Octonion (Quaternion, Quaternion) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary)
newtype It = It Octonion deriving (Eq, Ord, Num, Typeable, Fractional)
newtype ItFun = ItFun (It -> It) deriving (Arbitrary, CoArbitrary, Typeable)

instance Arbitrary It where arbitrary = fmap It it
instance CoArbitrary It where coarbitrary (It x) = coarbitrary x

(\\), (/) :: It -> It -> It
a / b = a * recip b
b \\ a = recip b * a

l, r, l1, r1, t :: It -> ItFun
l x = ItFun (\y -> x * y)
r x = ItFun (\y -> y * x)
l1 x = ItFun (\y -> x \\ y)
r1 x = ItFun (\y -> y / x)
t x = r x `compose` l1 x

compose :: ItFun -> ItFun -> ItFun
compose (ItFun f) (ItFun g) = ItFun (f . g)

obsItFun :: ItFun -> Gen It
obsItFun (ItFun f) = fmap f arbitrary

sig =
  signature {
    constants = [
       constant "1" (1 :: It),
       constant "*" ((*) :: It -> It -> It),
       --  constant "/" ((/) :: It -> It -> It),
       --  constant "\\" ((\\) :: It -> It -> It),
       constant "id" (ItFun id),
       (constant "l" l)   { conStyle = Uncurried },
       (constant "r" r)   { conStyle = Uncurried },
       (constant "l1" l1) { conStyle = Uncurried },
       (constant "r1" r1) { conStyle = Uncurried },
       (constant "t" t)   { conStyle = Uncurried },
       constant "." compose ],
    background = octBackground,
    maxTests = Just 5,
    instances = [
      inst (Sub Dict :: () :- Arbitrary ItFun),
      makeInstance (\() -> observe obsItFun),
      baseType (undefined :: It)]}
  where
    star = constant "*" ((*) :: It -> It -> It)
    lc = constant "l" l
    rc = constant "r" r
    dot = constant "." compose
    bi = Predicate "bi" (typeOf (undefined :: It -> It -> It -> Bool))
    x  = Var $ Variable 0 (typeOf (undefined :: It))
    y  = Var $ Variable 1 (typeOf (undefined :: It))
    a  = Var $ Variable 3 (typeOf (undefined :: It))
    b  = Var $ Variable 4 (typeOf (undefined :: It))
    c  = Var $ Variable 5 (typeOf (undefined :: It))
    octBackground = [
      [] :=>: bi :@: [x, y, x],
      [] :=>: bi :@: [x, y, y],
      [bi :@: [x, y, a],
       bi :@: [x, y, b]] :=>: bi :@: [x, y, Fun star [a, b]],
      [bi :@: [x, y, a],
       bi :@: [x, y, b],
       bi :@: [x, y, c]] :=>: Fun star [a, Fun star [b, c]] :=: Fun star [Fun star [a, b], c]]

main = quickSpec sig
