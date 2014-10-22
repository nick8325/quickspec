-- Arrays.

{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, DeriveDataTypeable #-}
import Test.QuickCheck
import Test.QuickSpec
import Data.Typeable
import Data.Array

put :: Ix i => i -> a -> Array i a -> Array i a
put ix v arr = arr // [(ix, v)]

arrays :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> [Sig]
arrays a = [
  -- Don't include head, or functions on natural numbers---they
  -- generate too many irrelevant terms.
  prelude (undefined :: a) `without` ["head", "*", "0", "1"],
  lists (undefined :: Int) `without` ["head"],

  ["x", "y", "z"] `vars` (undefined :: a),
  ["a"]           `vars` (undefined :: Array Int a),
  -- Generate ranges using a custom generator to improve test data
  -- distribution.
  ["r"]           `gvars` genRange,

  "!"             `fun2` ((!)       :: Array Int a -> Int -> a),
  "put"           `fun3` (put       :: Int -> a -> Array Int a -> Array Int a),
  "listArray"     `fun2` (listArray :: (Int, Int) -> [a] -> Array Int a),
  "elems"         `fun1` (elems     :: Array Int a -> [a]),
  "indices"       `fun1` (indices   :: Array Int a -> [Int])]

instance Arbitrary a => Arbitrary (Array Int a) where
  arbitrary = do
    (low, high) <- genRange
    elems <- arbitrary :: Gen (Int -> Maybe a)
    return (array (low, high) [(i, x) | i <- [low..high], Just x <- [elems i]])

genRange :: Gen (Int, Int)
genRange = do
  low <- choose (-2, 2)
  high <- fmap (low +) (choose (-1, 2))
  return (low, high)

-- Use Two instead of A to improve the chance of getting the right test data.
main = quickSpec (arrays (undefined :: Two))
