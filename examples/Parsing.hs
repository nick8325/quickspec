{-# LANGUAGE DeriveDataTypeable, TypeOperators, ScopedTypeVariables, StandaloneDeriving, TypeApplications #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import Data.List
import Text.ParserCombinators.ReadP
import Data.Constraint

deriving instance Typeable ReadP

instance Arbitrary a => Arbitrary (ReadP a) where
  arbitrary = fmap readS_to_P arbReadS

arbReadS :: Arbitrary a => Gen (String -> [(a, String)])
arbReadS = fmap convert (liftM2 (,) (elements [0..5]) arbitrary)
  where
    convert (n, parse) xs = take n [(x, drop n xs) | (x, n) <- parse xs]

obsReadP :: Ord a => String -> ReadP a -> [(a, String)]
obsReadP input parser =
  sort (readP_to_S parser input)

peek :: ReadP Char
peek = do
  (x:_) <- look
  return x

main = quickSpec [
  inst (Sub Dict :: Arbitrary A :- Arbitrary (ReadP A)),
  inst (\(Dict :: Dict (Ord A)) gen -> observe gen (obsReadP @ A)),

  background [
    con "return" (return :: A -> ReadP A),
    con "()" (),
    con "void" (void :: ReadP A -> ReadP ()),
    con "id" (id :: ReadP () -> ReadP ()),
    con ">>=" ((>>=) :: ReadP A -> (A -> ReadP B) -> ReadP B),
    con ">=>" ((>=>) :: (A -> ReadP B) -> (B -> ReadP C) -> A -> ReadP C) ],

  con "get" get,
  con "peek" peek,
  con "+++" ((+++) :: ReadP A -> ReadP A -> ReadP A),
  con "<++" ((<++) :: ReadP A -> ReadP A -> ReadP A),
  con "pfail" (pfail :: ReadP A),
  con "eof" eof ]

