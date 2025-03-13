-- Parser combinators.
-- Illustrates observational equality with polymorphic types.
{-# LANGUAGE DeriveDataTypeable, TypeOperators, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import QuickSpec.Internal
import Data.List
import Text.Parsec.Char
import Text.Parsec.String
import Text.Parsec.Prim
import Text.Parsec.Pos
import Text.Parsec.Error
import Data.Constraint
import Data.Functor.Identity
import Data.Ord

deriving instance Eq a => Eq (Consumed a)
deriving instance Ord a => Ord (Consumed a)
instance (Eq a, Eq b, Eq c) => Eq (Reply a b c) where
  x == y = toMaybe x == toMaybe y
instance (Ord a, Ord b, Ord c) => Ord (Reply a b c) where
  compare = comparing toMaybe
deriving instance (Eq a, Eq b) => Eq (State a b)
deriving instance (Ord a, Ord b) => Ord (State a b)

toMaybe (Ok x s _) = Just (x, s)
toMaybe (Error _) = Nothing

instance Arbitrary SourcePos where
  arbitrary = liftM3 newPos arbitrary arbitrary arbitrary

arbString :: Gen String
arbString = listOf (choose ('a', 'b'))

-- Generate random parsers.
instance Arbitrary (Parser String) where
  arbitrary = sized arb
    where
      arb :: Int -> Gen (Parser String)
      arb n =
        oneof $
          [ return <$> arbString ] ++
          [ liftM2 (>>) arb2 arb2 | n > 0 ] ++
          [ liftM2 (>>=) arb2 (resize (n `div` 2) arbitrary) | n > 0 ] ++
          [ string <$> arbString ] ++
          [ try <$> arb (n-1) | n > 0 ] ++
          [ liftM2 mplus arb2 arb2 | n > 0 ]
        where
          arb2 = arb (n `div` 2)

instance Arbitrary (State String ()) where
  arbitrary = liftM3 State arbString arbitrary arbitrary

-- Observational equality for parsers.
instance Ord a => Observe (State String ()) (Identity (Consumed (Identity (Reply String () a)))) (Parser a) where
  observe state parser = runParsecT parser state

main = quickSpec [
  inst (Sub Dict :: () :- Arbitrary (Parser String)),
  inst (Sub Dict :: Ord A :- Observe (State String ()) (Identity (Consumed (Identity (Reply String () A)))) (Parser A)),
  inst (Sub Dict :: () :- Arbitrary (State String ())),
  instFun (arbString :: Gen String),
  defaultTo (Proxy :: Proxy String),
  withMaxTermSize 7,
  withMaxTestSize 5,
  withMaxTests 10000,

--  background [
    --con "return" (return :: A -> Parser A),
--    con "()" (),
--    con "void" (void :: Parser A -> Parser ()),
  con ">>" ((>>) :: Parser A -> Parser B -> Parser B),
  con "<<|>" (\p q -> try p <|> q :: Parser A),
    --con "<|>" ((<|>) :: Parser A -> Parser A -> Parser A)],

--  con "string" (string :: String -> Parser String),
  con "try" (try :: Parser A -> Parser A)]

