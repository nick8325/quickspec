{-# LANGUAGE DeriveDataTypeable, TypeOperators, FlexibleInstances, GeneralizedNewtypeDeriving #-}
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

data Rat = Rat { mantissa :: Integer, exponent :: Int } deriving (Eq, Ord, Show, Typeable)
-- Rat x e = x / 2^e

rat :: Integer -> Int -> Rat
rat x e | e < 0 = error "rat: negative exponent"
rat x 0 = Rat x 0
rat x e | even x = rat (x `div` 2) (e-1)
rat x e = Rat x e

instance Arbitrary Rat where
  arbitrary = liftM2 rat arbitrary (choose (0, 10))
  shrink (Rat x e) = fmap (uncurry rat) (shrink (x, e))

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
type Object = (Vector, Vector, Vector, Word)

newtype Drawing = Drawing (Vector -> Vector -> Vector -> Objs) deriving Typeable
newtype Objs = Objs { unObjs :: Set Object } deriving (Eq, Ord, Typeable, Show)
instance Arbitrary Objs where arbitrary = fmap objs arbitrary

objs :: Set Object -> Objs
objs = Objs . Set.filter (\(_,b,c,_) -> b /= zero && c /= zero)

instance Show Drawing where
  show (Drawing x) = show (x one one one)
    where
      one = (Rat 1 0, Rat 1 0)

instance Arbitrary Drawing where
  arbitrary = do
    os <- arbitrary
    return . Drawing $ \x y z -> objs (Set.fromList [(x, y, z, o) | o <- os])
  shrink (Drawing f) =
    [ Drawing $ \x y z -> objs (Set.fromList [(x, y, z, o) | o <- objs'])
    | let os = [ o | (_, _, _, o) <- Set.toList (unObjs (f one one one)) ],
      objs' <- shrink os ]
    where
      one = (Rat 1 0, Rat 1 0)

blank :: Drawing
blank = Drawing (\_ _ _ -> objs Set.empty)

over, beside, above, above' :: Drawing -> Drawing -> Drawing
over (Drawing p) (Drawing q) = Drawing (\a b c -> p a b c `union` q a b c)
beside (Drawing p) (Drawing q) = Drawing (\a b c -> p a (half b) c `union` q (a `plus` half b) (half b) c)
above' (Drawing p) (Drawing q) = Drawing (\a b c -> p a b (half c) `union` q (a `plus` half c) b (half c))
above (Drawing p) (Drawing q) = Drawing (\a b c -> p (a `plus` half c) b (half c) `union` q a b (half c))

union :: Objs -> Objs -> Objs
union (Objs x) (Objs y) = objs (x `Set.union` y)

rot, flip, rot45 :: Drawing -> Drawing
rot (Drawing p) = Drawing (\a b c -> p (a `plus` b) c (neg b))
flip (Drawing p) = Drawing (\a b c -> p (a `plus` b) (neg b) c)
rot45 (Drawing p) = Drawing (\a b c -> p (a `plus` half (b `plus` c)) (half (b `plus` c)) (half (c `plus` neg b)))

quartet, quartet' :: Drawing -> Drawing -> Drawing -> Drawing -> Drawing
quartet a b c d = (a `beside` b) `above` (c `beside` d)
quartet' a b c d = (a `beside` b) `above'` (c `beside` d)

cycle, cycle' :: Drawing -> Drawing
cycle x = quartet x (rot (rot (rot x))) (rot x) (rot (rot x))
cycle' x = quartet' x (rot (rot (rot x))) (rot x) (rot (rot x))

obsDrawing :: Drawing -> Gen Objs
obsDrawing (Drawing d) = do
  (a, b, c) <- arbitrary
  return (d a b c)

sig1 =
  signature {
    maxTermSize = Just 7,
    instances = [
      makeInstance (\() -> NamesFor ["x", "y", "z", "w"] :: NamesFor Drawing),
      inst (Sub Dict :: () :- Arbitrary Drawing),
      makeInstance (\() -> observe obsDrawing) ],
    constants = [
      constant "over" over ]}

sig2 =
  signature {
    constants = [
      constant "beside" beside,
      -- constant "above" above' ]}
      constant "above" above ]}

sig3 =
  signature {
    constants = [
      constant "rot" rot ]}

sig4 =
  signature {
    constants = [
      constant "flip" flip ]}

sig5 =
  signature {
    constants = [
      constant "cycle" cycle,
      -- constant "cycle" cycle',
      constant "quartet" quartet ]}

sig6 =
  signature {
    constants = [
      constant "rot45" rot45 ]}

sig7 =
  signature {
    constants = [
      constant "blank" blank ]}

main = do
  thy1 <- quickSpec sig1
  thy2 <- quickSpec (thy1 `mappend` sig2)
  thy3 <- quickSpec (thy2 `mappend` sig3)
  thy4 <- quickSpec (thy3 `mappend` sig4)
  thy5 <- quickSpec (thy4 `mappend` sig5)
  {-thy6 <- quickSpec (thy5 `mappend` sig6)
  quickSpec (thy6 `mappend` sig7)-}
  return ()
