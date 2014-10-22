{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}
module Main where

import Control.Monad
import Data.Typeable
import Test.QuickCheck
import Test.QuickSpec

newtype Layout a = Layout [(Int, [a])] deriving (Typeable, Eq, Ord, Show)

instance Arbitrary a => Arbitrary (Layout a) where
  arbitrary = fmap Layout (liftM2 (:) arbitrary arbitrary)

text :: [a] -> Layout a
text s = Layout [(0, s)]

nest :: Int -> Layout a -> Layout a
nest k (Layout l) = Layout [(i+k, s) | (i, s) <- l]

($$) :: Layout a -> Layout a -> Layout a
Layout xs $$ Layout ys = Layout (xs ++ ys)

(<>) :: Layout a -> Layout a -> Layout a
Layout xs <> Layout ys = f (init xs) (last xs) (head ys) (tail ys)
  where f xs (i, s) (j, t) ys = Layout xs $$ Layout [(i, s ++ t)] $$ nest (i + length s - j) (Layout ys)

pretty :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> [Sig]
pretty a = [
  ["d","e","f"] `vars` (undefined :: Layout a),
  ["s","t","u"] `vars` (undefined :: [a]),
  ["n","m","o"] `vars` (undefined :: Int),
  "text" `fun1` (text :: [a] -> Layout a),
  "nest" `fun2` (nest :: Int -> Layout a -> Layout a),
  "$$" `fun2` (($$) :: Layout a -> Layout a -> Layout a),
  "<>" `fun2` ((<>) :: Layout a -> Layout a -> Layout a),
  background [
    "[]" `fun0` ([] :: [a]),
    "++" `fun2` ((++) :: [a] -> [a] -> [a]),
    "0" `fun0` (0 :: Int),
    "length" `fun1` (length :: [a] -> Int),
    "+" `fun2` ((+) :: Int -> Int -> Int)]]

main = quickSpec (pretty (undefined :: Two))
