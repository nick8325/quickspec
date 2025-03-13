-- Note: we'd like to find zero divisor laws of the form t*u = 0.
-- QuickSpec finds e.g.
--   20. (x + ih) * (1 + ih) = (x + 1) * (1 + ih)
-- where setting x=-1 makes the RHS 0, but we'd like to find
--       (-1 + ih) * (1 + ih) = 0
-- Maybe use templates here?
--
-- A simple example testing arithmetic functions.
{-# LANGUAGE TupleSections #-}
import QuickSpec
import QuickSpec.Internal
import qualified QuickSpec.Internal.Haskell as Haskell
import Test.QuickCheck
import Twee.Pretty
import Control.Monad

data BiComplex = B Rational Rational Rational Rational
  deriving (Eq, Ord, Show)

instance Arbitrary BiComplex where
  arbitrary =
    resize 2 $ do
      n <- choose (0, 4)
      elts <- take n <$> shuffle [0..3]
      let
        arb0 i
         | i `elem` elts = oneof [arbitrary, elements [1, -1, 1/3, -1/3]]
         | otherwise = return 0
      liftM4 B (arb0 0) (arb0 1) (arb0 2) (arb0 3)

instance Num BiComplex where
  fromInteger n = B (fromInteger n) 0 0 0
  negate (B r i h ih) = B (-r) (-i) (-h) (-ih)
  B r1 i1 h1 ih1 + B r2 i2 h2 ih2 =
    B (r1+r2) (i1+i2) (h1+h2) (ih1+ih2)
  B r1 i1 h1 ih1 * B r2 i2 h2 ih2 =
    B r i h ih
    where
      r  = r1*r2  - i1*i2  - h1*h2  + ih1*ih2
      i  = r1*i2  + r2*i1  - h1*ih2 - h2*ih1 
      h  = r1*h2  + r2*h1  - i1*ih2 - i2*ih1
      ih = r1*ih2 + r2*ih1 + i1*h2  + i2*h1

i, h :: BiComplex
i = B 0 1 0 0
h = B 0 0 1 0

conj1, conj2, conj3 :: BiComplex -> BiComplex
conj1 (B r i h ih) = B r (-i) h (-ih)
conj2 (B r i h ih) = B r i (-h) (-ih)
conj3 = conj1 . conj2
norm1, norm2 :: BiComplex -> BiComplex
norm1 x = x * conj1 x
norm2 x = x * conj2 x

isReal (B _ 0 0 0) = True
isReal _ = False

genReal = do
  B x _ _ _ <- arbitrary
  return (B x 0 0 0)

isDuplex  (B _ 0 0 _) = True
isDuplex _ = False

genDuplex = do
  B x _ _ y <- arbitrary
  return (B x 0 0 y)

main = quickSpec [
  withMaxTermSize 7,
  -- withMaxTests 10000,
  monoType (Proxy :: Proxy BiComplex),
  series [
    [con "0" (0 :: BiComplex),
     con "1" (1 :: BiComplex),
     -- con "+" ((+) :: BiComplex -> BiComplex -> BiComplex),
     con "-" (negate :: BiComplex -> BiComplex),
     con "*" ((*) :: BiComplex -> BiComplex -> BiComplex)],
    [con "real" isReal,
    -- con "duplex" isDuplex,
     con "True" True],
     --predicateGen "duplex" isDuplex (\() -> do { x <- genDuplex; return (x, ()) })],
    [con "conj1" conj1,
     con "conj2" conj2,
     con "conj3" conj3],
    [con "norm1" norm1,
     con "norm2" norm2],
    [con "10" (10 :: BiComplex)],
    [--con "-1" (-1 :: BiComplex),
     con "i" (i :: BiComplex),
     con "h" (h :: BiComplex),
     con "ih" (i * h :: BiComplex)]]]
