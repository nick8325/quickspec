-- Utilities for testing functions that return partial results.
{-# LANGUAGE DeriveDataTypeable, ExistentialQuantification, DefaultSignatures #-}
module Test.QuickSpec.Approximate where

import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils
import Test.QuickSpec.Utils.Typeable
import Control.Spoon
import Control.Applicative hiding (Const)
import System.Random
import Data.Monoid

data Schema a
  = Const a
  | forall b. App (Schema (b -> a)) (Schema b)
  | Plug (Either (Gen a) (Schema a))

instance Functor Schema where
  fmap f x = pure f <*> x

instance Applicative Schema where
  pure = Const
  (<*>) = App

class (Typeable a, Arbitrary a, Eq a) => Partial a where
  unlifted :: a -> Schema a
  unlifted x = Const x

lifted :: Partial a => a -> Schema a
lifted x = Plug $
  case soupspoon (unlifted x) of
    Nothing -> Left (coarbitraryShow (typeOf x) arbitrary) 
    Just s -> Right s
  where
    soupspoon x =
      case teaspoon x of
        Just (Const y) -> fmap Const (spoony y)
        y -> y

instance Partial ()
instance Partial Int
instance Partial Integer
instance Partial Bool

instance Partial a => Partial [a] where
  unlifted [] = pure []
  unlifted (x:xs) = (:) <$> lifted x <*> lifted xs

approximate :: Partial a => (StdGen, Int) -> a -> a
approximate (g, n) x = aux (lifted x)
  where
    aux :: Schema a -> a
    aux (Const x) = x
    aux (App f x) = aux f (aux x)
    aux (Plug (Left gen)) = unGen gen g n
    aux (Plug (Right s)) = aux s

pobserver :: (Ord a, Partial a) => a -> Sig
pobserver x = observerSig (Observer (MkGen f))
  where f g n y = approximate (g, n `max` 50) (y `asTypeOf` x)

genPartial :: Partial a => a -> Gen a
genPartial = aux . lifted
  where
    aux :: Schema a -> Gen a
    aux (Const x) = return x
    aux (App f x) = aux f <*> aux x
    aux (Plug (Left _)) = undefined
    aux (Plug (Right x)) = frequency [(1, undefined), (3, aux x)]

pvars :: (Ord a, Partial a) => [String] -> a -> Sig
pvars xs w = 
  pobserver w
  `mappend` gvars xs ((arbitrary `asTypeOf` return w) >>= genPartial)
