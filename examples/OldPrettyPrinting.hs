{-# LANGUAGE DeriveDataTypeable, TypeOperators #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec hiding (background, (<>), text, nest, ($$))

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

nesting :: Layout a -> Int
nesting (Layout ((i,_):_)) = i

background =
  signature {
    constants = [
       constant "[]" ([] :: [A]),
       constant "++" ((++) :: [A] -> [A] -> [A]),
       constant "0" (0 :: Int),
       constant "+" ((+) :: Int -> Int -> Int),
       constant "length" (length :: [A] -> Int) ]}

sig =
  signature {
    constants = [
       constant "text" (text :: [A] -> Layout A),
       constant "nest" (nest :: Int -> Layout A -> Layout A),
       constant "nesting" (nesting :: Layout A -> Int),
       constant "$$" (($$) :: Layout A -> Layout A -> Layout A),
       constant "<>" ((<>) :: Layout A -> Layout A -> Layout A) ],
    instances = [
      inst (Sub Dict :: Ord A         :- Ord       (Layout A)),
      inst (Sub Dict :: Arbitrary A   :- Arbitrary (Layout A)) ],
    defaultTo = Just (typeOf (undefined :: Bool)) }

main = quickSpecWithBackground background sig
