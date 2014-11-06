{-# LANGUAGE DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
import QuickSpec
import Test.QuickCheck
import System.Random
import Data.Monoid

class Group a where
  ident :: a
  op :: a -> a -> a
  inv :: a -> a
  gyr :: a -> a -> a -> a

newtype Gyrogroup = G Int deriving (Eq, Ord, Typeable, CoArbitrary, Enum, Num, Random, Real, Integral, Show)

instance Arbitrary Gyrogroup where
  arbitrary = choose (1, 16)

gident :: Gyrogroup
gident = 1

b = (,)

f :: Int -> Int -> (Int, Int)
f 1 1 = b 1 2
f 1 2 = b 3 4
f 1 3 = b 5 6
f 1 4 = b 7 8
f 1 5 = b 9 10
f 1 6 = b 11 12
f 1 7 = b 13 14
f 1 8 = b 15 16
f 2 1 = b 3 4
f 2 2 = b 2 1
f 2 3 = b 7 8
f 2 4 = b 6 5
f 2 5 = b 12 11
f 2 6 = b 9 10
f 2 7 = b 16 15
f 2 8 = b 13 14
f 3 1 = b 5 6
f 3 2 = b 7 8
f 3 3 = b 4 3
f 3 4 = b 1 2
f 3 5 = b 16 15
f 3 6 = b 13 14
f 3 7 = b 10 9
f 3 8 = b 12 11
f 4 1 = b 7 8
f 4 2 = b 6 5
f 4 3 = b 1 2
f 4 4 = b 3 4
f 4 5 = b 14 13
f 4 6 = b 16 15
f 4 7 = b 11 12
f 4 8 = b 10 9
f 5 1 = b 9 10
f 5 2 = b 11 12
f 5 3 = b 13 14
f 5 4 = b 15 16
f 5 5 = b 1 2
f 5 6 = b 3 4
f 5 7 = b 5 6
f 5 8 = b 7 8
f 6 1 = b 11 12
f 6 2 = b 10 9
f 6 3 = b 15 16
f 6 4 = b 14 13
f 6 5 = b 4 3
f 6 6 = b 1 2
f 6 7 = b 8 7
f 6 8 = b 5 6
f 7 1 = b 13 14
f 7 2 = b 15 16
f 7 3 = b 12 11
f 7 4 = b 9 10
f 7 5 = b 7 8
f 7 6 = b 6 5
f 7 7 = b 1 2
f 7 8 = b 3 4
f 8 1 = b 15 16
f 8 2 = b 14 13
f 8 3 = b 9 10
f 8 4 = b 11 12
f 8 5 = b 5 6
f 8 6 = b 7 8
f 8 7 = b 4 3
f 8 8 = b 1 2

gop :: Gyrogroup -> Gyrogroup -> Gyrogroup
gop (G x) (G y)
  | x `mod` 2 == y `mod` 2 = G a
  | otherwise = G b
  where
    (a, b) = f ((x+1) `div` 2) ((y+1) `div` 2)

ginv :: Gyrogroup -> Gyrogroup
ginv x = head [ y | y <- [1..16], op y x == ident ]

ggyr :: Gyrogroup -> Gyrogroup -> Gyrogroup -> Gyrogroup
ggyr x y
  | x >= 5 && x <= 8 && y >= 9 = a
  | y >= 5 && y <= 8 && x >= 9 = a
  | x >= 9 && x <= 12 && y >= 13 = a
  | y >= 9 && y <= 12 && x >= 13 = a
  | otherwise = id
  where
    a z
      | z <= 8 = z
      | even z = z-1
      | otherwise = z+1

instance Group Gyrogroup where
  ident = gident
  op = gop
  inv = ginv
  gyr = ggyr

instance Group Int where
  ident = 0
  op = (+)
  inv = negate
  gyr _ _ = id

instance (Group a, Group b) => Group (a, b) where
  ident = (ident, ident)
  op (x, x') (y, y') = (op x y, op x' y')
  inv (x, y) = (inv x, inv y)
  gyr (x, x') (y, y') (z, z') = (gyr x y z, gyr x' y' z')

props :: (Eq a, Group a) => a -> a -> a -> [Bool]
props a b c = [
  ident `op` a == a,
  a `op` ident == a,
  inv a `op` a == ident,
  a `op` (b `op` c) == (a `op` b) `op` gyr a b c,
  (a `op` b) `op` c == a `op` (b `op` gyr b a c),
  gyr a b c == gyr (a `op` b) b c,
  gyr a b c == gyr a (b `op` a) c,
  inv (a `op` b) == gyr a b (inv b `op` inv a)]

type It = (Gyrogroup, Int)

sig0 =
  signature {
    instances = [baseType (undefined :: It)],
    maxTermSize = Just 8,
    maxTests = Just 500 }

sig1 =
  sig0 {
    constants = [
       constant "0" (ident :: It),
       constant "+" (op :: It -> It -> It) ]}

sig2 =
  sig0 {
    constants = [
       constant "-" (inv :: It -> It) ]}

sig3 =
  sig0 {
    constants = [
       (constant "gyr" (gyr :: It -> It -> It -> It)) { conStyle = Gyrator } ]}

sig4 =
  sig0 {
    constants = [
       constant "[+]" (\a b -> a `op` gyr a (inv b) b :: It) ]}

main = do
  thy1 <- quickSpec sig1
  thy2 <- quickSpec (thy1 `mappend` sig2)
  thy3 <- quickSpec (thy2 `mappend` sig3)
  thy4 <- quickSpec (thy3 `mappend` sig4)
  return ()
