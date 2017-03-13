{-# LANGUAGE TypeApplications #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import Data.Dynamic

sig =
  signature {
    maxTermSize = Just 4,
    maxPruningSize = Just 10,
    constants = [
       constant "poh" foo,
       constant "bar" bar,
       constant "baz" baz
    ],
    predicates = [
                  predicate "p" p
                 ]
   }

foo :: Int -> Int
foo 0  = bar
foo 1 = bar
foo x = bar + x

bar :: Int
bar = -10

baz :: Int -> Int -> Int
baz _ _ = 1

p :: Int -> Bool
p x = (x == 0) || (x == 1)

main = quickSpec sig
