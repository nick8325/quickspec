{-# LANGUAGE DeriveDataTypeable, TypeOperators #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import Data.Proxy

newtype Layout = Layout [(Int, String)]
  deriving (Typeable, Eq, Ord, Show)

instance Arbitrary Layout where
  arbitrary = fmap Layout (liftM2 (:) arbitrary arbitrary)

text :: String -> Layout
text s = Layout [(0, s)]

nest :: Int -> Layout -> Layout
nest k (Layout l) = Layout [(i+k, s) | (i, s) <- l]

($$) :: Layout -> Layout -> Layout
Layout xs $$ Layout ys = Layout (xs ++ ys)

(<>) :: Layout -> Layout -> Layout
Layout xs <> Layout ys =
  combine (init xs) (last xs) (head ys) (tail ys)
  where
    combine xs (i, s) (j, t) ys =
      Layout xs $$
      Layout [(i, s ++ t)] $$
      nest (i + length s - j) (Layout ys)

nesting :: Layout -> Int
nesting (Layout ((i,_):_)) = i

main =
  quickSpec [
    withMaxTermSize 9,
    baseType (Proxy :: Proxy Layout),
    constant "\"\"" "",
    constant "++" ((++) :: [A] -> [A] -> [A]),
    constant "0" (0 :: Int),
    constant "+" ((+) :: Int -> Int -> Int),
    constant "length" (length :: [A] -> Int),
    constant "text" text,
    constant "nest" nest,
    constant "$$" ($$),
    constant "<>" (<>) ]
