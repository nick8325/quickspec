-- | The main QuickSpec module. Everything you need to run QuickSpec lives here.
--
-- To run QuickSpec, you need to tell it which functions to test. We call the
-- list of functions the /signature/. Here is an example signature, which tells
-- QuickSpec to test the @++@, @reverse@ and @[]@ functions:
--
-- @
-- sig = [
--   `con` "++"      ((++) :: [`A`] -> [`A`] -> [`A`]),
--   `con` "reverse" (reverse :: [`A`] -> [`A`]),
--   `con` "[]"      ([] :: [`A`]) ]
-- @
--
-- The `con` function, used above, adds a function to the signature, given its
-- name and its value. When declaring polymorphic functions in the signature,
-- we use the types `A` to `E` to represent type variables.
-- Having defined this signature, we can say @`quickSpec` sig@ to test it and
-- see the discovered equations.
--
-- If you want to test functions over your own datatypes, those types need to
-- implement `Arbitrary` and `Ord` (if the `Ord` instance is a problem, see `Observe`).
-- You must also declare those instances to QuickSpec, by including them in the
-- signature. For monomorphic types you can do this using `monoType`:
--
-- @
-- data T = ...
-- main = quickSpec [
--   ...,
--   `monoType` (Proxy :: Proxy T)]
-- @
--
-- You can only declare monomorphic types with `monoType`. If you want to test
-- your own polymorphic types, you must explicitly declare `Arbitrary` and `Ord`
-- instances using the `inst` function.
--
-- You can also use QuickSpec to find conditional equations. To do so, you need
-- to include some /predicates/ in the signature. These are functions returning
-- `Bool` which can appear as conditions in other equations. Declaring a predicate
-- works just like declaring a function, except that you declare it using
-- `predicate` instead of `con`.
--
-- You can also put certain options in the signature. The most useful is
-- `withMaxTermSize', which you can use to tell QuickSpec to generate larger
-- equations.
--
-- The @<https://github.com/nick8325/quickspec/tree/master/examples examples>@
-- directory contains many examples. Here are some interesting ones:
--
-- * @<https://github.com/nick8325/quickspec/tree/master/examples/Arith.hs Arith.hs>@: a simple arithmetic example. Demonstrates basic use of QuickSpec.
-- * @<https://github.com/nick8325/quickspec/tree/master/examples/Lists.hs Lists.hs>@: list functions. Demonstrates testing polymorphic functions.
-- * @<https://github.com/nick8325/quickspec/tree/master/examples/Sorted.hs Sorted.hs>@: sorting. Demonstrates finding conditional equations.
-- * @<https://github.com/nick8325/quickspec/tree/master/examples/IntSet.hs IntSet.hs>@: a few functions from "Data.IntSet". Demonstrates testing user-defined datatypes and finding conditional equations.
-- * @<https://github.com/nick8325/quickspec/tree/master/examples/PrettyPrinting.hs PrettyPrinting.hs>@: pretty printing combinators. Demonstrates testing user-defined datatypes and using observational equality.
-- * @<https://github.com/nick8325/quickspec/tree/master/examples/Parsing.hs Parsing.hs>@: parser combinators. Demonstrates testing polymorphic datatypes and using observational equality.
--
-- You can also find some larger case studies in our paper,
-- <http://www.cse.chalmers.se/~nicsma/papers/quickspec2.pdf Quick specifications for the busy programmer>.

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
module QuickSpec(
  -- * Running QuickSpec
  quickSpec, Sig, Signature(..),

  -- * Declaring functions and predicates
  con, predicate, predicateGen,
  -- ** Type variables for polymorphic functions
  A, B, C, D, E,

  -- * Declaring types
  monoType, monoTypeObserve, vars, monoTypeWithVars, inst, Observe(..),

  -- * Standard signatures
  -- | The \"prelude\": a standard signature containing useful functions
  --   like '++', which can be used as background theory.
  lists, arith, funs, bools, prelude, without,

  -- * Exploring functions in series
  background, series,

  -- * Including type class constraints (experimental, subject to change)
  type (==>), liftC, instanceOf,

  -- * Customising QuickSpec
  withMaxTermSize, withMaxTests, withMaxTestSize, defaultTo,
  withPruningDepth, withPruningTermSize, withFixedSeed,
  withInferInstanceTypes,

  -- * Re-exported functionality
  Typeable, (:-)(..), Dict(..), Proxy(..), Arbitrary) where

import QuickSpec.Internal
import QuickSpec.Internal.Haskell(Observe(..))
import QuickSpec.Internal.Type(A, B, C, D, E)
import Data.Typeable
import Data.Constraint
import Test.QuickCheck
