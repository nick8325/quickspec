-- Utilities for testing functions that return partial results.
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving, ScopedTypeVariables #-}
module Test.QuickSpec.Approximate where

import Test.QuickCheck
import Test.QuickCheck.Modifiers
import Test.QuickSpec.Signature
import Data.Typeable
import Control.Spoon

deriving instance Typeable1 NonNegative

class (Typeable a, Ord a) => Approximate a where
  approximate :: Int -> a -> a
  approximate _ = id

instance Approximate () where
instance Approximate Int where
instance Approximate Integer where
instance Approximate Bool where

instance Approximate a => Approximate [a] where
  approximate n = take n . map (approximate n)

newtype Approximants a = Approximants a deriving Typeable

instance Approximate a => Eq (Approximants a) where
  x == y = x `compare` y == EQ

instance Approximate a => Ord (Approximants a) where
  compare x y = eval n x `compare` eval n y
    where
      eval n (Approximants x) = teaspoon ((y == y) `seq` y)
        where y = approximate n x

      n = search 0 100

      -- binary search from m inclusive to n exclusive
      -- important property: if eval n x = Nothing then eval (n+1) x = Nothing
      search m n
        | m > n = m
        | otherwise =
          case (eval mid x, eval mid y) of
            (Nothing, Nothing) -> search m mid
            (Just x', Just y') | x' == y' -> search (mid+1) n
            _ -> mid
        where mid = (m + n) `div` 2

-- Wrapper functions around 'observer'.

approximate1 :: forall a. Approximate a => a -> Sig
approximate1 _ = observer1 (Approximants :: a -> Approximants a)

approximate2 :: forall a b. (Arbitrary a, Typeable a, Approximate b) =>
                (a -> b) -> Sig
approximate2 f = observer1 (Approximants . f)