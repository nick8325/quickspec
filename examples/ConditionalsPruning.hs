{-# LANGUAGE TypeApplications #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import Data.Dynamic

sig =
  signature {
    maxTermSize = Just 8,
    constants = [
       constant "poo" foo,
       constant "bar" bar,
       constant "baz" baz
    ],
    predicates = [-- predicateGen "notNull" ((not . null) :: [Int] -> Bool) notNullGen,
                  predicateGen "p" p genP
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

genP :: Gen [Dynamic]
genP = elements [[toDyn (0 :: Int)], [toDyn (1 :: Int)]]

main = quickSpec sig
