{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickSpec
import Test.QuickSpec
import Test.QuickCheck
import Data.Typeable

bools = [
  ["x", "y", "z"] `vars` (undefined :: Bool),

  "||"    `fun2` (||),
  "&&"    `fun2` (&&),
  "not"   `fun1` not,
  "True"  `fun0` True,
  "False" `fun0` False]

arith :: forall a. (Typeable a, Ord a, Num a, Arbitrary a) => a -> [Sig]
arith _ = [
  ["x", "y", "z"] `vars` (undefined :: a),

  "0" `fun0` (0   :: a),
  "1" `fun0` (1   :: a),
  "+" `fun2` ((+) :: a -> a -> a),
  "*" `fun2` ((*) :: a -> a -> a)]

lists :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> [Sig]
lists _ = [
  ["xs", "ys", "zs"] `vars` (undefined :: [a]),

  "[]"      `fun0` ([]      :: [a]),
  ":"       `fun2` ((:)     :: a -> [a] -> [a]),
  "unit"    `fun1` (return  :: a -> [a]),
  "++"      `fun2` ((++)    :: [a] -> [a] -> [a]),
  "length"  `fun1` (length  :: [a] -> Int),
  "reverse" `fun1` (reverse :: [a] -> [a]),
  "map"     `fun2` (map     :: (a -> a) -> [a] -> [a])
  ]

funs :: forall a. (Typeable a, Ord a, Arbitrary a, CoArbitrary a) => a -> [Sig]
funs _ = [
  vars ["f", "g", "h"] (undefined :: a -> a),

  -- We treat . as a function of two arguments here (blind2)---i.e.,
  -- we do not generate terms of the form (f . g) x.
  blind2 "."   ((.) :: (a -> a) -> (a -> a) -> (a -> a)),

  -- Similarly, id is not treated as a function.
  blind0 "id"  (id  :: a -> a),

  -- Tell QuickSpec how to compare values of function type:
  -- i.e., generate a random argument and apply the function to it.
  observer1 $ \x (f :: a -> a) -> f x
  ]

main = mapM_ quickSpec $ [
  bools,
  arith (undefined :: Int),
  funs (undefined :: Int),
  [vars ["x", "y", "z"] 'A', -- i.e. at type Char
   silence (funs 'A'),
   silence (arith (undefined :: Int)),
   signature (lists 'A')]]
