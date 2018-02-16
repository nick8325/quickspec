{-# LANGUAGE DeriveDataTypeable, TypeOperators, FlexibleInstances, GeneralizedNewtypeDeriving #-}
import QuickSpec
import Test.QuickCheck
import qualified Data.Set as Set
import Data.Set(Set)
import Prelude hiding (flip, cycle)
import Data.Monoid
import Control.Monad
import Data.Word
import Data.Constraint

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

obsDrawing :: (Vector, Vector, Vector) -> Drawing -> Objs
obsDrawing (a, b, c) (Drawing d) = d a b c

main =
  quickSpec [
    inst (Sub Dict :: () :- Arbitrary Drawing),
    inst (\gen -> observe gen obsDrawing),
    inst (Sub Dict :: () :- Arbitrary (Vector, Vector, Vector)),
    inst (Sub Dict :: () :- Ord Objs),
    series [sig1, sig2, sig3, sig4, sig5, sig6, sig7] ]
  where
    sig1 = [con "over" over]
    sig2 = [
      con "beside" beside,
      -- con "above" above',
      con "above" above]
    sig3 = [con "rot" rot]
    sig4 = [con "flip" flip]
    sig5 = [
      con "cycle" cycle,
      -- con "cycle" cycle',
      con "quartet" quartet]
    sig6 = [con "rot45" rot45]
    sig7 = [con "blank" blank]
