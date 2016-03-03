{-# LANGUAGE DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
import QuickSpec hiding (Constant)
import Test.QuickCheck
import Data.Monoid

newtype Constant = Constant Integer deriving (Eq, Ord, Typeable, Num)
instance Arbitrary Constant where
  arbitrary = fmap (Constant . getPositive) arbitrary

sig1 =
  signature {
    maxTermSize = Just 9,
    --extraPruner = Just (SPASS 1),
    constants = [
      constant "+" ((+) :: Integer -> Integer -> Integer),
      --constant "negate" (negate :: Integer -> Integer),
      constant "+" ((+) :: Constant -> Constant -> Constant),
      --constant "0" (0 :: Integer),
      --constant "1" (1 :: Constant),
      --constant "2" (2 :: Constant),
      constant "*" (\(Constant x) y -> x * y) ],
    instances = [baseTypeNames ["c", "d", "e"] (undefined :: Constant)] }
    
sig2 =
  signature {
    constants = [
      constant "min" (min :: Integer -> Integer -> Integer),
      constant "max" (max :: Integer -> Integer -> Integer) ]}

main = quickSpecWithBackground sig1 sig2
