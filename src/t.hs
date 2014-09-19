{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, DeriveDataTypeable, ScopedTypeVariables #-}
import Data.Ratio
import Test.QuickSpec
import Test.QuickCheck
import Control.Monad
import Prelude hiding ((/), (\\))
import qualified Prelude
import Data.Typeable
import Octonions
import Test.QuickSpec.Eval
import Test.QuickSpec.Signature hiding (sig)
import qualified Test.QuickSpec.Signature as S
import Data.Monoid

(\\), (/) :: It -> It -> It
a / b = a * recip b
b \\ a = recip b * a

l, r, l1, r1 :: It -> Fun
l x = Fun (\y -> x * y)
r x = Fun (\y -> y * x)
l1 x = Fun (\y -> x \\ y)
r1 x = Fun (\y -> y / x)

sig = mconcat [
  constant "1" (1 :: It),
  constant "*" ((*) :: It -> It -> It),
  constant "/" ((/) :: It -> It -> It),
  constant "\\" ((\\) :: It -> It -> It),
  ord (undefined :: It),
  arb (undefined :: It)]

sig2 = mconcat [
  constant "0" (0 :: Int),
  constant "1" (1 :: Int),
  constant "+" ((+) :: Int -> Int -> Int),
  constant "*" ((*) :: Int -> Int -> Int),
  ord (undefined :: Int),
  arb (undefined :: Int)]

main = quickSpec S.sig

{-
sig1 = [
  withDepth 4,
  withTests 10,
  ["a", "b", "c"] `vars` (undefined :: It),
  "1" `fun0` (1 :: It),
  "*" `fun2` ((*) :: It -> It -> It),
  "/" `fun2` ((/) :: It -> It -> It),
  "\\" `fun2` ((\\) :: It -> It -> It)]

sig2 = [
  withSize 3,
  withDepth 4,
  withTests 10,
  ["f", "g", "h"] `vars` (undefined :: Fun),
  ["a", "b", "c"] `vars` (undefined :: It),
  observer2 (\x (Fun f :: Fun) -> f x),
  "*" `fun2` ((*) :: It -> It -> It),
  "1" `fun0` (1 :: It),
  "1" `blind0` (Fun (\x -> x)),
  "." `blind2` (\(Fun f) (Fun g) -> Fun (\x -> f (g x))),
  "l" `blind1` l,
  "r" `blind1` r,
  "l1" `blind1` l1,
  "r1" `blind1` r1]
-}
