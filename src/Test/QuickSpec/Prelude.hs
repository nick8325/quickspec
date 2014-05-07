-- | The \"prelude\": a standard signature containing useful functions
--   like '++', which can be used as background theory.

{-# LANGUAGE ScopedTypeVariables, DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
module Test.QuickSpec.Prelude where

import Test.QuickSpec.Signature
import Test.QuickSpec.Approximate
import Test.QuickCheck
import Data.Typeable

-- | Just a type.
--   You can instantiate your polymorphic functions at this type
--   to include them in a signature.
newtype A = A Int deriving (Eq, Ord, Typeable, Arbitrary, CoArbitrary, Show)
newtype B = B Int deriving (Eq, Ord, Typeable, Arbitrary, CoArbitrary, Show)
newtype C = C Int deriving (Eq, Ord, Typeable, Arbitrary, CoArbitrary, Show)

instance Partial A where unlifted (A x) = fmap A (unlifted x)
instance Partial B where unlifted (B x) = fmap B (unlifted x)
instance Partial C where unlifted (C x) = fmap C (unlifted x)

-- | A type with two elements.
--   Use this instead of @A@ if testing doesn't work well because
--   the domain of @A@ is too large.
data Two = One | Two deriving (Eq, Ord, Typeable, Show)

instance Arbitrary Two where
  arbitrary = elements [One, Two]

instance CoArbitrary Two where
  coarbitrary One = variant 0
  coarbitrary Two = variant (-1)

-- | A signature containing boolean functions:
-- @(`||`)@, @(`&&`)@, `not`, `True`, `False`.
bools :: Sig
bools = background [
  ["x", "y", "z"] `vars` (undefined :: Bool),

  "||"    `fun2` (||),
  "&&"    `fun2` (&&),
  "not"   `fun1` not,
  "True"  `fun0` True,
  "False" `fun0` False]

-- | A signature containing arithmetic operations:
-- @0@, @1@, @(`+`)@, @(`*`)@.
-- Instantiate it with e.g. @arith (undefined :: `Int`)@.
arith :: forall a. (Typeable a, Ord a, Num a, Arbitrary a) => a -> Sig
arith _ = background [
  ["x", "y", "z"] `vars` (undefined :: a),

  "0" `fun0` (0   :: a),
  "1" `fun0` (1   :: a),
  "+" `fun2` ((+) :: a -> a -> a),
  "*" `fun2` ((*) :: a -> a -> a)]

-- | A signature containing list operations:
-- @[]@, @(:)@, `head`, `tail`, @(`++`)@.
-- Instantiate it with e.g. @lists (undefined :: `A`)@.
lists :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> Sig
lists _ = background [
  ["xs", "ys", "zs"] `vars` (undefined :: [a]),

  "[]"      `fun0` ([]      :: [a]),
  ":"       `fun2` ((:)     :: a -> [a] -> [a]),
  "head"    `fun1` (head    :: [a] -> a),
  "tail"    `fun1` (tail    :: [a] -> [a]),
  "++"      `fun2` ((++)    :: [a] -> [a] -> [a])]

-- | A signature containing higher-order functions:
-- @(`.`)@, `id`, and some function variables.
-- Useful for testing `map`.
funs :: forall a. (Typeable a, Ord a, Arbitrary a, CoArbitrary a) => a -> Sig
funs _ = background [
  ["f", "g", "h"] `vars` (undefined :: a -> a),

  "."  `blind2` ((.) :: (a -> a) -> (a -> a) -> (a -> a)),
  "id" `blind0` (id  :: a -> a),

  observer2 (\(x :: a) (f :: a -> a) -> f x)
  ]

-- | The QuickSpec prelude.
-- Contains boolean, arithmetic and list functions,
-- and some variables.
-- Instantiate it as e.g. @prelude (undefined :: `A`)@.
prelude :: (Typeable a, Ord a, Arbitrary a) => a -> Sig
prelude a = background [
  ["x", "y", "z"] `vars` a,
  bools,
  arith (undefined :: Int),
  lists a ]
