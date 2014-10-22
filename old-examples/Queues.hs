{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickSpec hiding (lists)
import Test.QuickCheck
import Data.Typeable
import Prelude hiding (fst)

enq x ys = ys ++ [x]
deq (x:xs) = xs
fst (x:xs) = x

main = quickSpec [
  vars ["x","y"] (undefined :: A),
  vars ["f","g","h"] (undefined :: [A] -> [A]),
  vars ["f","g","h"] (undefined :: [A] -> A),
  "enq" `blind1` (enq :: A -> [A] -> [A]),
  "deq" `blind0` (deq :: [A] -> [A]),
  "fst" `blind0` (fst :: [A] -> A),
  "."   `blind2` ((.) :: ([A] -> [A]) -> ([A] -> [A]) -> [A] -> [A]),
  "."   `blind2` ((.) :: ([A] -> A) -> ([A] -> [A]) -> [A] -> A),
  -- "id"  `blind0` (id :: [A] -> [A]),
  observer2 (\(x::[A]) (f::[A]->A) -> f x),
  observer2 (\(x::[A]) (f::[A]->[A]) -> f x),
  -- "empty" `fun0` ([] :: [A]),
  withDepth 4,
  withSize 7
  ]

-- main = quickCheck prop

-- prop :: Int -> Int -> [Int] -> Bool
-- prop x y q = fst (enq y (enq x q)) == fst (enq x q)
