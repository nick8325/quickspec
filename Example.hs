{-# LANGUAGE ScopedTypeVariables #-}

import QuickSpec
import Signature
import Data.Monoid
import Test.QuickCheck
import Data.Typeable

bools = [
  vars ["x", "y", "z"] True,
  fun2 "||" (||),
  fun2 "&&" (&&),
  fun1 "not" not, 
  fun0 "True" True,
  fun0 "False" False]

arith :: forall a. (Typeable a, Ord a, Num a, Arbitrary a) => a -> [Sig]
arith _ = [
  vars ["x", "y", "z"] (undefined :: a),
  fun0 "0" (0 :: a),
  fun0 "1" (1 :: a),
  fun2 "+" ((+) :: a -> a -> a),
  fun2 "*" ((*) :: a -> a -> a)]

lists :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> [Sig]
lists _ = [
  vars ["xs", "ys", "zs"] (undefined :: [a]),
  fun1 "length" (length :: [a] -> Int),
  fun1 "reverse" (reverse :: [a] -> [a]),
  fun2 "++" ((++) :: [a] -> [a] -> [a]),
  fun0 "[]" ([] :: [a]),
  fun2 "map" (map :: (a -> a) -> [a] -> [a]),
  fun1 "unit" (return :: a -> [a])]

funs :: forall a. (Typeable a, Ord a, Arbitrary a, CoArbitrary a) => a -> [Sig]
funs ty = [
  vars ["f", "g", "h"] (undefined :: a -> a),
  blind2 "." (\(f :: a -> a) (g :: a -> a) -> f . g),
  blind0 "id" (id :: a -> a),
  observer2 (\(x :: a) (f :: a -> a) -> f x)
  ]

main = mapM_ quickSpec $ [
  bools,
  arith (undefined :: Int),
  funs (undefined :: Int),
  [silence (funs 'A'),
   silence (arith (undefined :: Int)),
   signature (lists 'A')]]
