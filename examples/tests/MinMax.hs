{-# LANGUAGE DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
import QuickSpec
import Test.QuickCheck
import Data.Monoid
import Data.Typeable

newtype Constant = Constant Integer deriving (Eq, Ord, Typeable, Num)
instance Arbitrary Constant where
  arbitrary = fmap (Constant . getPositive) arbitrary

main = quickSpec [
  withMaxTermSize 9,
  series [sig1, sig2] ]

sig1 = [
  con "+" ((+) :: Integer -> Integer -> Integer),
  --con "negate" (negate :: Integer -> Integer),
  con "+" ((+) :: Constant -> Constant -> Constant),
  --con "0" (0 :: Integer),
  --con "1" (1 :: Constant),
  --con "2" (2 :: Constant),
  con "*" (\(Constant x) y -> x * y),
  monoTypeWithVars ["c", "d", "e"] (Proxy :: Proxy Constant) ]
    
sig2 = [
  con "min" (min :: Integer -> Integer -> Integer),
  con "max" (max :: Integer -> Integer -> Integer) ]
