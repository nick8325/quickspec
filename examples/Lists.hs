{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickSpec hiding (lists)
import Test.QuickCheck
import Data.Typeable

lists :: forall a. (Typeable a, Ord a, Arbitrary a, CoArbitrary a) =>
         a -> [Sig]
lists a = [
  arith (undefined :: Int),
  funs (undefined :: a),

  ["x", "y", "z"] `vars` (undefined :: a),
  ["xs", "ys", "zs"] `vars` (undefined :: [a]),

  "[]"      `fun0` ([]      :: [a]),
  ":"       `fun2` ((:)     :: a -> [a] -> [a]),

  "head"    `fun1` (head    :: [a] -> a),
  "tail"    `fun1` (tail    :: [a] -> [a]),
  "unit"    `fun1` (return  :: a -> [a]),
  "++"      `fun2` ((++)    :: [a] -> [a] -> [a]),
  "length"  `fun1` (length  :: [a] -> Int),
  "reverse" `fun1` (reverse :: [a] -> [a]),
  "map"     `fun2` (map     :: (a -> a) -> [a] -> [a])
  ]

main = quickSpec (lists (undefined :: A))
