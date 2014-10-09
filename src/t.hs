{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, DeriveDataTypeable, ScopedTypeVariables #-}
import Data.Ratio
import QuickSpec
import Test.QuickCheck
import Control.Monad
import Prelude hiding ((/), (\\))
import qualified Prelude
import Data.Typeable
import Octonions
import QuickSpec.Type
import QuickSpec.Eval
import QuickSpec.Signature hiding (sig)
import qualified QuickSpec.Signature as S
import Data.Monoid hiding ((<>))
import PrettyPrinting

(\\), (/) :: It -> It -> It
a / b = a * recip b
b \\ a = recip b * a

l, r, l1, r1, t :: It -> Fun
l x = Fun (\y -> x * y)
r x = Fun (\y -> y * x)
l1 x = Fun (\y -> x \\ y)
r1 x = Fun (\y -> y / x)
t x = r x `compose` l1 x

compose :: Fun -> Fun -> Fun
compose (Fun f) (Fun g) = Fun (f . g)

sig = mconcat [
  constant "rev" (reverse :: [A] -> [A]),
  constant "app" ((++) :: [A] -> [A] -> [A]),
  constant "[]" ([] :: [A]),
  --arb (undefined :: Int -> Int),
  --constant "map" (map :: (Int -> Int) -> [Int] -> [Int]),
  --constant "sort" (sort :: [Int] -> [Int]),
  --constant "usort" (usort :: [Int] -> [Int]),
  inst (undefined :: Int),
  inst (undefined :: [Int])]

sig2 = mconcat [
  constant "1" (1 :: It),
  constant "*" ((*) :: It -> It -> It),
--  constant "/" ((/) :: It -> It -> It),
--  constant "\\" ((\\) :: It -> It -> It),
  constant "id" (Fun id),
  constant "l" l,
  constant "r" r,
  constant "l1" l1,
  constant "r1" r1,
  constant "t" t,
  constant "." compose,
  inst (undefined :: Int),
  inst (undefined :: Fun),
  inst (undefined :: It)]

sig3 = mconcat [
  constant "0" (0 :: Int),
  constant "1" (1 :: Int),
  constant "+" ((+) :: Int -> Int -> Int),
  constant "*" ((*) :: Int -> Int -> Int),
  inst (undefined :: Int)]

sig4 = mconcat [
  constant "text" (text :: [Bool] -> Layout Bool),
  constant "nest" (nest :: Int -> Layout Bool -> Layout Bool),
  constant "$$" (($$) :: Layout Bool -> Layout Bool -> Layout Bool),
  constant "<>" ((<>) :: Layout Bool -> Layout Bool -> Layout Bool),
  constant "[]" ([] :: [Bool]),
  constant "++" ((++) :: [Bool] -> [Bool] -> [Bool]),
  constant "0" (0 :: Int),
  constant "+" ((+) :: Int -> Int -> Int),
  constant "length" (length :: [Bool] -> Int),
  inst (undefined :: Layout Bool),
  inst (undefined :: [Bool]),
  inst (undefined :: Int)]

main = quickSpec sig

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
