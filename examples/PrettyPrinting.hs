{-# LANGUAGE DeriveDataTypeable, TypeOperators, StandaloneDeriving #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec hiding (background, (<>), text, nest, ($$))
import Text.PrettyPrint.HughesPJ

deriving instance Typeable Doc

instance Arbitrary Doc where
  arbitrary =
    sized $ \n ->
      let bin = resize (n `div` 2) arbitrary
          un = resize (n-1) arbitrary in
      oneof $
        [ liftM2 ($$) bin bin | n > 0 ] ++
        [ liftM2 (<>) bin bin | n > 0 ] ++
        [ liftM2 nest arbitrary un | n > 0 ] ++
        [ fmap text arbString ]

arbString :: Gen String
arbString = listOf (elements "ab")

background =
  signature {
    maxTests = Just 1000,
    constants = [
       constant "[]" ([] :: [A]),
       constant "++" ((++) :: [A] -> [A] -> [A]),
       constant "0" (0 :: Int),
       constant "+" ((+) :: Int -> Int -> Int),
       -- FIXME why does this not work when we use [A]?
       constant "length" (length :: [Char] -> Int) ]}

obsDoc :: Doc -> Gen String
obsDoc d = do
  n <- arbitrary
  return (show (text "" $$ nest n d))

sig =
  signature {
    maxTests = Just 1000,
    constants = [
       constant "text" text,
       constant "nest" nest,
       constant "$$" ($$),
       constant "<>" (<>) ],
    instances = [
      makeInstance (\() -> arbString),
      makeInstance (\() -> observe obsDoc),
      inst (Sub Dict :: () :- Arbitrary Doc) ],
    defaultTo = Just (typeOf (undefined :: Bool)) }

main = quickSpecWithBackground background sig
