-- Utilities for testing functions that return partial results.
{-# LANGUAGE DeriveDataTypeable, ExistentialQuantification, DefaultSignatures #-}
module Test.QuickSpec.Approximate where

import Test.QuickCheck
import Test.QuickSpec.Signature
import Data.Typeable
import Control.Spoon
import Data.Default
import Control.Applicative hiding (Const)

data Schema a
  = Const a
  | forall b. App (Schema (b -> a)) (Schema b)
  | Plug a (Schema a)

instance Functor Schema where
  fmap f x = pure f <*> x

instance Applicative Schema where
  pure = Const
  (<*>) = App

class Partial a where
  lifted :: a -> Schema a

  default lifted :: Default a => a -> Schema a
  lifted x = Plug def (unlifted x)

  unlifted :: a -> Schema a
  unlifted x = Const x

instance Partial () where
instance Partial Int where
instance Partial Integer where
instance Default Bool where def = False
instance Partial Bool where

instance Partial a => Partial [a] where
  unlifted [] = pure []
  unlifted (x:xs) = (:) <$> lifted x <*> lifted xs

partial :: Schema a -> Gen a
partial (Const x) = return x
partial (App f x) = partial f <*> partial x
partial (Plug _ x) = frequency [(1, undefined), (3, partial x)]

pvars :: (Arbitrary a, Typeable a, Partial a) => [String] -> a -> Sig
pvars xs w = gvars xs $ (arbitrary `asTypeOf` return w) >>= partial . lifted