{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
module QuickSpec(module QuickSpec, Typeable, A, B, C, D, E, Predicateable, TestCase) where

import QuickSpec.Haskell(Predicateable, TestCase)
import qualified QuickSpec.Haskell as Haskell
import qualified QuickSpec.Haskell.Resolve as Haskell
import qualified QuickSpec.Testing.QuickCheck as QuickCheck
import qualified QuickSpec.Pruning.UntypedTwee as Twee
import Test.QuickCheck
import Data.Constraint
import Data.Lens.Light
import QuickSpec.Utils
import QuickSpec.Type
import QuickSpec.Term

newtype Sig = Sig (Haskell.Config -> Haskell.Config)

instance Monoid Sig where
  mempty = Sig id
  Sig sig1 `mappend` Sig sig2 = Sig (sig2 . sig1)

class Signature sig where
  toSig :: sig -> Sig

instance Signature Sig where
  toSig = id

instance Signature sig => Signature [sig] where
  toSig = mconcat . map toSig

baseType :: forall proxy a. (Ord a, Arbitrary a, Typeable a) => proxy a -> Sig
baseType _ =
  mconcat [
    inst (Dict :: Dict (Ord a)),
    inst (Dict :: Dict (Arbitrary a))]

inst :: Typeable a => a -> Sig
inst x =
  Sig (modL Haskell.lens_instances (`mappend` Haskell.inst x))

constant :: Typeable a => String -> a -> Sig
constant name x =
  Sig (modL Haskell.lens_constants (++ [Haskell.constant name x]))

predicate :: ( Predicateable a
             , Typeable a
             , Typeable (TestCase a))
             => String -> a -> Sig
predicate name x =
  Sig (modL Haskell.lens_predicates (++ [Haskell.predicate name x]))

withMaxTests :: Int -> Sig
withMaxTests n =
  Sig (setL (QuickCheck.lens_num_tests # Haskell.lens_quickCheck) n)

withMaxTestSize :: Int -> Sig
withMaxTestSize n =
  Sig (setL (QuickCheck.lens_max_test_size # Haskell.lens_quickCheck) n)

withPruningDepth :: Int -> Sig
withPruningDepth n =
  Sig (setL (Twee.lens_max_cp_depth # Haskell.lens_twee) n)

withPruningTermSize :: Int -> Sig
withPruningTermSize n =
  Sig (setL (Twee.lens_max_term_size # Haskell.lens_twee) n)

withMaxTermSize :: Int -> Sig
withMaxTermSize n = Sig (setL Haskell.lens_max_size n)

defaultTo :: Typeable a => proxy a -> Sig
defaultTo proxy = Sig (setL Haskell.lens_default_to (typeRep proxy))

quickSpec :: Signature sig => sig -> IO ()
quickSpec signature =
  Haskell.quickSpec (sig Haskell.defaultConfig)
  where
    Sig sig = toSig signature
