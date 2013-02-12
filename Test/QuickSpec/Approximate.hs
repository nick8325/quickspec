-- Utilities for testing functions that return partial results.
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
module Test.QuickSpec.Approximate where

import Test.QuickCheck
import Test.QuickCheck.Modifiers
import Test.QuickSpec.Signature
import Data.List
import Data.Typeable

deriving instance Typeable1 NonNegative

class (Typeable a, Ord a) => Approximate a where
  approximate :: NonNegative Int -> a -> a
  approximate _ = id

instance Approximate () where
instance Approximate Int where
instance Approximate Integer where
instance Approximate Bool where

instance Approximate a => Approximate [a] where
  approximate n = genericTake n . map (approximate n)

approximant :: Approximate a => a -> NonNegative Int -> a -> a
approximant _ = approximate

-- Wrapper functions around 'observer'.

approximate1 :: Approximate a => a -> Sig
approximate1 x = observer2 (approximant x)

approximate2 :: (Arbitrary a, Typeable a, Approximate b) =>
                (a -> b) -> Sig
approximate2 f = observer3 (approximant . f)