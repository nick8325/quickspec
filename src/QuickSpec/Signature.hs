-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module QuickSpec.Signature where

#include "errors.h"
import Data.Constraint
import QuickSpec.Term
import QuickSpec.Type
import Data.Functor.Identity
import Data.Monoid
import Test.QuickCheck

newtype Instance c a = Instance (Dict (c a))
data Signature =
  Signature {
    constants :: [Constant],
    ords      :: [Value (Instance Ord)],
    arbs      :: [Value (Instance Arbitrary)] }

instance Monoid Signature where
  mempty = Signature [] [] []
  Signature cs os as `mappend` Signature cs' os' as' = Signature (cs++cs') (os++os') (as++as')

constant :: Typeable a => String -> a -> Signature
constant name x = Signature [Constant name (toValue (Identity x))] [] []

ord :: forall a. (Typeable a, Ord a) => a -> Signature
ord _ = Signature [] [toValue (Instance Dict :: Instance Ord a)] []

arb :: forall a. (Typeable a, Arbitrary a) => a -> Signature
arb _ = Signature [] [] [toValue (Instance Dict :: Instance Arbitrary a)]

inst :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> Signature
inst x = ord x `mappend` arb x
