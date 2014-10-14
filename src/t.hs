{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, DeriveDataTypeable, ScopedTypeVariables #-}
import Data.Ratio
import QuickSpec
import Test.QuickCheck
import Control.Monad
import Prelude hiding ((/), (\\))
import qualified Prelude
import Data.Typeable hiding (typeOf)
import Octonions
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Base hiding (text, (<>), compose, nest)
import QuickSpec.Eval
import QuickSpec.Test
import QuickSpec.Prop
import QuickSpec.Signature hiding (sig)
import qualified QuickSpec.Signature as S
import Data.Monoid hiding ((<>))
import PrettyPrinting

(\\), (/) :: It -> It -> It
a / b = a * recip b
b \\ a = recip b * a

l, r, l1, r1, t :: It -> ItFun
l x = ItFun (\y -> x * y)
r x = ItFun (\y -> y * x)
l1 x = ItFun (\y -> x \\ y)
r1 x = ItFun (\y -> y / x)
t x = r x `compose` l1 x

compose :: ItFun -> ItFun -> ItFun
compose (ItFun f) (ItFun g) = ItFun (f . g)

listsSig = mconcat [
  constant "rev" (reverse :: [A] -> [A]),
  constant "app" ((++) :: [A] -> [A] -> [A]),
  constant "[]" ([] :: [A]),
  arb (undefined :: Default -> Default),
  constant "map" (map :: (A -> B) -> [A] -> [B]),
  inst (undefined :: Default),
  inst (undefined :: [Default])]

constSig = mconcat [
  constant "const" ((\x y -> [const x y]) :: A -> B -> [A]),
  constant "asTypeOf" ((\x y -> [asTypeOf x y]) :: A -> A -> [A]),
  inst (undefined :: [Int]),
  inst (undefined :: Int)]

boolSig = mconcat [
  constant "True" True,
  constant "False" False,
  constant "||" (||),
  constant "&&" (&&),
  constant "not" not,
  inst (undefined :: Int),
  inst (undefined :: Bool),
  inst (undefined :: Default)]

octSig = (mconcat [
  constant "1" (1 :: It),
  constant "*" ((*) :: It -> It -> It),
--  constant "/" ((/) :: It -> It -> It),
--  constant "\\" ((\\) :: It -> It -> It),
  constant "id" (ItFun id),
  constant "l" l,
  constant "r" r,
  constant "l1" l1,
  constant "r1" r1,
  constant "t" t,
  constant "." compose,
  inst (undefined :: Int),
  inst (undefined :: ItFun),
  inst (undefined :: It),
  inst (undefined :: Default) ]) { background = octBackground }
  where
    star = mkConstant "*" ((*) :: It -> It -> It)
    lc = mkConstant "l" l
    rc = mkConstant "r" r
    dot = mkConstant "." compose
    bi = Predicate "bi" (typeOf (undefined :: It -> It -> It -> Bool))
    x  = Var $ Variable 0 (typeOf (undefined :: It))
    y  = Var $ Variable 1 (typeOf (undefined :: It))
    a  = Var $ Variable 3 (typeOf (undefined :: It))
    b  = Var $ Variable 4 (typeOf (undefined :: It))
    c  = Var $ Variable 5 (typeOf (undefined :: It))
    octBackground = [
      [] :=>: bi :@: [x, y, x],
      [] :=>: bi :@: [x, y, y],
      [bi :@: [x, y, a],
       bi :@: [x, y, b]] :=>: bi :@: [x, y, Fun star [a, b]],
      [bi :@: [x, y, a],
       bi :@: [x, y, b],
       bi :@: [x, y, c]] :=>: Fun star [a, Fun star [b, c]] :=: Fun star [Fun star [a, b], c]]

data Table9Point1 = I | A | B | C | D deriving (Eq, Ord, Typeable)

instance Arbitrary Table9Point1 where
  arbitrary = elements [I, A, B, C, D]

times :: Table9Point1 -> Table9Point1 -> Table9Point1
times I I = I
times I A = A
times I B = B
times I C = C
times I D = D
times A I = A
times A A = A
times A B = B
times A C = D
times A D = D
times B I = B
times B A = B
times B B = D
times B C = A
times B D = A
times C I = C
times C A = D
times C B = A
times C C = B
times C D = B
times D I = D
times D A = D
times D B = A
times D C = B
times D D = B

table9point1 = mconcat [
  constant "times" times,
  constant "i" I,
  constant "a" A,
  constant "b" B,
  constant "c" C,
  constant "d" D,
  inst (undefined :: Default),
  inst (undefined :: Table9Point1) ]

arithSig = mconcat [
  constant "0" (0 :: Int),
  constant "1" (1 :: Int),
  constant "+" ((+) :: Int -> Int -> Int),
  constant "*" ((*) :: Int -> Int -> Int),
  inst (undefined :: Int),
  inst (undefined :: Default)]

prettyBackgroundSig = mconcat [
  constant "[]" ([] :: [Bool]),
  constant "++" ((++) :: [Bool] -> [Bool] -> [Bool]),
  constant "0" (0 :: Int),
  constant "+" ((+) :: Int -> Int -> Int),
  constant "length" (length :: [Bool] -> Int),
  inst (undefined :: [Bool]),
  inst (undefined :: Int),
  inst (undefined :: Default)]

prettySig = prettyBackgroundSig `mappend` mconcat [
  constant "text" (text :: [Bool] -> Layout Bool),
  constant "nest" (nest :: Int -> Layout Bool -> Layout Bool),
  constant "$$" (($$) :: Layout Bool -> Layout Bool -> Layout Bool),
  constant "<>" ((<>) :: Layout Bool -> Layout Bool -> Layout Bool),
  inst (undefined :: Layout Bool) ]

main = do
  eqs <- quickSpec prettyBackgroundSig
  quickSpec prettySig { background = eqs }

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
