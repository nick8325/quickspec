-- Parser combinators.
-- Illustrates observational equality with polymorphic types.
{-# LANGUAGE DeriveDataTypeable, TypeOperators, ScopedTypeVariables, StandaloneDeriving #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec hiding (background, (<>), text, nest, ($$))
import Data.List
import Text.ParserCombinators.ReadP
import Data.Typeable
import Data.Constraint

deriving instance Typeable ReadP

-- Generate random parsers.
instance Arbitrary a => Arbitrary (ReadP a) where
  arbitrary = fmap readS_to_P arbReadS

arbReadS :: Arbitrary a => Gen (String -> [(a, String)])
arbReadS = fmap convert (liftM2 (,) (elements [0..5]) arbitrary)
  where
    convert (n, parse) xs = take n [(x, drop n xs) | (x, n) <- parse xs]

-- Observational equality for parsers.
obsReadP :: Ord a => ReadP a -> Gen [(a, String)]
obsReadP parser = do
  input <- arbitrary
  return (sort (readP_to_S parser input))

peek :: ReadP Char
peek = do
  (x:_) <- look
  return x

bg =
  signature {
    instances = mconcat [
      inst (Sub Dict :: Arbitrary A :- Arbitrary (ReadP A)),
      inst (\(Dict :: Dict (Ord A)) -> observe (obsReadP :: ReadP A -> Gen [(A, String)]))],

    constants = [
      constant "return" (return :: A -> ReadP A),
      constant "()" (),
      constant "void" (void :: ReadP A -> ReadP ()),
      constant "id" (id :: ReadP () -> ReadP ()),
      constant ">>=" ((>>=) :: ReadP A -> (A -> ReadP B) -> ReadP B),
      constant ">=>" ((>=>) :: (A -> ReadP B) -> (B -> ReadP C) -> A -> ReadP C) ]}

sig =
  signature {
    constants = [
      constant "get" get,
      constant "peek" peek,
      constant "+++" ((+++) :: ReadP A -> ReadP A -> ReadP A),
      constant "<++" ((<++) :: ReadP A -> ReadP A -> ReadP A),
      constant "pfail" (pfail :: ReadP A),
      constant "eof" eof ]}

main = quickSpecWithBackground bg sig
