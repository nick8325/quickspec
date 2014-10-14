-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module QuickSpec.Signature where

#include "errors.h"
import Data.Constraint
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Prop
import Data.Functor.Identity
import Data.Monoid
import Test.QuickCheck hiding (subterms)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Char hiding (ord)

newtype Instance c a = Instance (Dict (c a))
data Signature =
  Signature {
    constants  :: [Constant],
    ords       :: [Value (Instance Ord)],
    arbs       :: [Value (Instance Arbitrary)],
    background :: [Prop] }

instance Monoid Signature where
  mempty = Signature [] [] [] []
  Signature cs os as b `mappend` Signature cs' os' as' b' = Signature (cs++cs') (os++os') (as++as') (b++b')

signature :: Signature
signature = mempty

constant :: Typeable a => String -> a -> Constant
constant name x = Constant name value (poly value) (arity (typeOf x)) pretty
  where
    value = toValue (Identity x)
    pretty
      | head name == ',' = tupleOp (arity (typeOf x))
      | isOp name = infixOp 5
      | otherwise = flip prettyPrecGenericApp

isOp :: String -> Bool
isOp "[]" = False
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_'

ord :: forall a. (Typeable a, Ord a) => a -> Value (Instance Ord)
ord _ = toValue (Instance Dict :: Instance Ord a)

arb :: forall a. (Typeable a, Arbitrary a) => a -> Value (Instance Arbitrary)
arb _ = toValue (Instance Dict :: Instance Arbitrary a)

inst :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> Signature
inst x = signature { ords = [ord x], arbs = [arb x] }

typeUniverse :: Signature -> Set Type
typeUniverse sig =
  Set.fromList $
    Var (TyVar 0):
    [ oneTypeVar (typ t) | c <- constants sig, t <- subterms (typ c) ]
