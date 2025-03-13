-- The octonions, made using the Cayley-Dickson construction.
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses #-}
import Data.Ratio
import QuickSpec
import Test.QuickCheck
import Twee.Pretty
import Control.Monad
import Data.Proxy

newtype SmallRational = SmallRational Rational
  deriving (Eq, Ord, Num, Typeable, Fractional, Conj, CoArbitrary, Show)
instance Arbitrary SmallRational where
  arbitrary = SmallRational <$> liftM2 (%) arbitrary (arbitrary `suchThat` (/= 0))

-- A class for types with conjugation, a norm operator and a generator.
class Fractional a => Conj a where
  conj :: a -> a
  norm :: a -> Rational
  it :: Gen a

instance Conj Rational where
  conj x = x
  norm x = x*x
  -- Only generate small rationals for efficiency.
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

newtype Complex = Complex (SmallRational, SmallRational) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)
newtype Quaternion = Quaternion (Complex, Complex) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)
newtype Octonion = Octonion (Quaternion, Quaternion) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)

newtype It = It Octonion deriving (Eq, Ord, Num, Typeable, Fractional, Conj, CoArbitrary, Show)

instance Arbitrary It where
  -- Division is undefined on zero octonions.
  arbitrary = It <$> resize 1 (arbitrary `suchThat` (/= 0))

data Op = L It | R It | Inverse | Compose [Op]

instance Arbitrary Op where
  arbitrary =
    fmap (Compose . take 5) $ listOf $ oneof
      [L <$> arbitrary,
       R <$> arbitrary,
       return Inverse]

eval :: Op -> It -> It
eval (L x) y = x * y
eval (R y) x = x * y
eval Inverse x = recip x
eval (Compose ops) x = foldr (.) id (map eval ops) x

invert :: Op -> Op
invert (L x) = L (recip x)
invert (R x) = R (recip x)
invert Inverse = Inverse
invert (Compose ops) = Compose (map invert (reverse ops))

instance Observe It It Op where
  observe x op = eval op x

main = quickSpec [
  -- Make the pruner more powerful, which is helpful when Doing Maths
  --withPruningTermSize 9,
  withMaxTermSize 11,
  monoType (Proxy :: Proxy It),
  monoTypeObserve (Proxy :: Proxy Op),
  -- One test suffices :)
  withMaxTests 100,
  series [
    [con "*" ((*) :: It -> It -> It),
     con "inv" (recip :: It -> It),
     con "1" (1 :: It)],
    [con "l" L,
     con "r" R,
     con "j" Inverse,
     con "jconj" (\f -> Compose [Inverse, f, Inverse]),
     con "t" (\x -> Compose $ reverse [R x, invert (L x)]),
     con "l2" (\x y -> Compose [L x, L y, invert (L (y * x))]),
     con "r2" (\x y -> Compose $ reverse [R x, R y, invert (R (x * y))]),
     con "c" (\x y -> Compose [R x, L y, R (recip x), L (recip y)]),
     con "inverted" invert,
     con "id" (Compose []),
     con "." (\f g -> Compose [f, g])],
     --con "inv" (recip :: It -> It),
     --con "1" (1 :: It)],
    [{-con "@" eval-} ]]]
