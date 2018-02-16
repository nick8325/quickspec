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

newtype Sig = Sig (Int -> Haskell.Config -> Haskell.Config)

instance Monoid Sig where
  mempty = Sig (\_ -> id)
  Sig sig1 `mappend` Sig sig2 = Sig (\n -> sig2 n . sig1 n)

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
  Sig (\_ -> modL Haskell.lens_instances (`mappend` Haskell.inst x))

appendAt :: Int -> a -> [[a]] -> [[a]]
appendAt n x [] = appendAt n x [[]]
appendAt 0 x (xs:xss) = (xs ++ [x]):xss
appendAt n x (xs:xss) = xs:appendAt (n-1) x xss

constant :: Typeable a => String -> a -> Sig
constant name x =
  Sig (\n -> modL Haskell.lens_constants (appendAt n (Haskell.constant name x)))

predicate :: ( Predicateable a
             , Typeable a
             , Typeable (TestCase a))
             => String -> a -> Sig
predicate name x =
  Sig (\n -> modL Haskell.lens_predicates (appendAt n (Haskell.predicate name x)))

first :: Signature sig => sig -> Sig
first signature =
  Sig (\n -> sig (n+1))
  where
    Sig sig = toSig signature

withMaxTests :: Int -> Sig
withMaxTests n =
  Sig (\_ -> setL (QuickCheck.lens_num_tests # Haskell.lens_quickCheck) n)

withMaxTestSize :: Int -> Sig
withMaxTestSize n =
  Sig (\_ -> setL (QuickCheck.lens_max_test_size # Haskell.lens_quickCheck) n)

withPruningDepth :: Int -> Sig
withPruningDepth n =
  Sig (\_ -> setL (Twee.lens_max_cp_depth # Haskell.lens_twee) n)

withPruningTermSize :: Int -> Sig
withPruningTermSize n =
  Sig (\_ -> setL (Twee.lens_max_term_size # Haskell.lens_twee) n)

withMaxTermSize :: Int -> Sig
withMaxTermSize n = Sig (\_ -> setL Haskell.lens_max_size n)

defaultTo :: Typeable a => proxy a -> Sig
defaultTo proxy = Sig (\_ -> setL Haskell.lens_default_to (typeRep proxy))

quickSpec :: Signature sig => sig -> IO ()
quickSpec signature =
  Haskell.quickSpec (sig 0 Haskell.defaultConfig)
  where
    Sig sig = toSig signature
