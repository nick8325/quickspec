{-# LANGUAGE DeriveDataTypeable, TypeOperators #-}
import QuickSpec
import Test.QuickCheck
import qualified Data.Set as Set
import Data.Set(Set)
import Prelude hiding (flip, cycle)
import Data.Monoid
import Control.Monad
import Data.Word

class Half a where
  zero :: a
  neg :: a -> a
  plus :: a -> a -> a
  half :: a -> a

instance (Half a, Half b) => Half (a, b) where
  zero = (zero, zero)
  neg (x, y) = (neg x, neg y)
  plus (x, y) (z, w) = (plus x z, plus y w)
  half (x, y) = (half x, half y)

data Rat = Rat { mantissa :: Integer, exponent :: Int } deriving (Eq, Ord, Show)
-- Rat x e = x / 2^e

rat :: Integer -> Int -> Rat
rat x e | e < 0 = error "rat: negative exponent"
rat x 0 = Rat x 0
rat x e | even x = rat (x `div` 2) (e-1)
rat x e = Rat x e

instance Arbitrary Rat where
  arbitrary = liftM2 rat arbitrary (choose (0, 10))

instance CoArbitrary Rat where
  coarbitrary (Rat x e) = coarbitrary x . coarbitrary e

instance Half Rat where
  zero = rat 0 0
  neg (Rat x e) = Rat (negate x) e
  plus (Rat x1 e1) (Rat x2 e2) =
    rat (x1 * 2^(e - e1) + x2 * 2^(e - e2)) e
    where
      e = e1 `max` e2
  half (Rat x e) = Rat x (e+1)

type Vector = (Rat, Rat)
type Object = Word

newtype Drawing = Drawing (Vector -> Vector -> Vector -> Set Object) deriving Typeable

instance Show Drawing where
  show (Drawing x) = show (x one one one)
    where
      one = (Rat 1 0, Rat 1 0)

instance Arbitrary Drawing where
  arbitrary = fmap Drawing arbitrary

instance (Ord a, Arbitrary a) => Arbitrary (Set a) where
  arbitrary = fmap Set.fromList arbitrary

blank :: Drawing
blank = Drawing (\_ _ _ -> Set.empty)

over, beside, above :: Drawing -> Drawing -> Drawing
over (Drawing p) (Drawing q) = Drawing (\a b c -> p a b c `Set.union` q a b c)
beside (Drawing p) (Drawing q) = Drawing (\a b c -> p a (half b) c `Set.union` q (a `plus` half b) (half b) c)
above (Drawing p) (Drawing q) = Drawing (\a b c -> p a b (half c) `Set.union` q (a `plus` half c) b (half c))

rot, flip, rot45 :: Drawing -> Drawing
rot (Drawing p) = Drawing (\a b c -> p (a `plus` b) c (neg b))
flip (Drawing p) = Drawing (\a b c -> p (a `plus` b) (neg b) c)
rot45 (Drawing p) = Drawing (\a b c -> p (a `plus` half (b `plus` c)) (half (b `plus` c)) (half (c `plus` neg b)))

quartet :: Drawing -> Drawing -> Drawing -> Drawing -> Drawing
quartet a b c d = (a `beside` b) `above` (c `beside` d)

cycle :: Drawing -> Drawing
cycle x = quartet x (rot (rot (rot x))) (rot x) (rot (rot x))

obsDrawing :: Drawing -> Gen (Set Object)
obsDrawing (Drawing d) = do
  (a, b, c) <- arbitrary
  return (d a b c)

sig1 =
  signature {
    maxTermSize = Just 7,
    instances = [
      inst (Sub Dict :: () :- Arbitrary Drawing),
      makeInstance (\() -> observe obsDrawing) ],
    constants = [
      constant "over" over,
      constant "rot" rot ]}

sig2 =
  signature {
    constants = [
      constant "beside" beside,
      constant "above" above ]}

sig3 =
  signature {
    constants = [
      constant "flip" flip ]}

sig4 =
  signature {
    constants = [
      constant "quartet" quartet,
      constant "cycle" cycle ]}

main = do
  thy1 <- quickSpec sig1
  thy2 <- quickSpec (thy1 `mappend` sig2)
  thy3 <- quickSpec (thy2 `mappend` sig3)
  quickSpec (thy3 `mappend` sig4)
