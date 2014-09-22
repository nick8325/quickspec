{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}
module PrettyPrinting where

import Control.Monad
import Data.Typeable
import Test.QuickCheck

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
