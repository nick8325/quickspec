-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Test.QuickSpec.Signature where

#include "errors.h"
import Data.Constraint
import Test.QuickSpec.Term
import Test.QuickSpec.Type
import Data.Functor.Identity
import Data.Monoid
import Test.QuickCheck
import Data.Typeable
import Control.Monad

data Instance = forall c. Typeable c => Instance (Dict c)
data Signature =
  Signature {
    constants :: [Constant],
    instances :: [Instance] }

instance Monoid Signature where
  mempty = Signature [] []
  Signature cs is `mappend` Signature cs' is' = Signature (cs++cs') (is++is')

constant :: Typeable a => String -> a -> Signature
constant name x = Signature [Constant name (toValue (Identity x))] []

instance_ :: Typeable c => Dict c -> Signature
instance_ d = Signature [] [Instance d]

-- :)
deriving instance Typeable Ord
deriving instance Typeable Arbitrary

ord :: forall a. (Typeable a, Ord a) => a -> Signature
ord _ = instance_ (Dict :: Dict (Ord a))

arb :: forall a. (Typeable a, Arbitrary a) => a -> Signature
arb _ = instance_ (Dict :: Dict (Arbitrary a))

findInstance :: Typeable c => Signature -> Maybe (Dict c)
findInstance sig = msum [ gcast d | Instance d <- instances sig ]

-- Testing!
sig :: Signature
sig = mconcat [
  constant "rev" (reverse :: [A] -> [A]),
  constant "app" ((++) :: [A] -> [A] -> [A]),
  ord (undefined :: [Int]),
  arb (undefined :: [Int])]
