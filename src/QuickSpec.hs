
-- | The main QuickSpec module.
--
-- For many examples of use, see the @examples@ directory in the source distribution,
-- which you can also find at <https://github.com/nick8325/quickspec/blob/master/examples>.

{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
module QuickSpec(
  -- * Running QuickSpec
  quickSpec,
  Sig, Signature(..),

  -- * Declaring functions and predicates
  con, predicate, Predicateable, TestCase,

  -- * Declaring types
  baseType, baseTypeNames, inst, Names(..), observe,
  Typeable, (:-)(..), Dict(..), A, B, C, D, E, Proxy(..),

  -- * Exploring functions in series
  background, series,

  -- * Customising QuickSpec
  withMaxTests, withMaxTestSize, withPruningDepth, withPruningTermSize, withMaxTermSize, defaultTo, withFixedSeed) where

import QuickSpec.Haskell(Predicateable, TestCase, Names(..), observe)
import qualified QuickSpec.Haskell as Haskell
import qualified QuickSpec.Haskell.Resolve as Haskell
import qualified QuickSpec.Testing.QuickCheck as QuickCheck
import qualified QuickSpec.Pruning.UntypedTwee as Twee
import Test.QuickCheck
import Test.QuickCheck.Random
import System.Random.TF.Gen
import Data.Constraint
import Data.Lens.Light
import QuickSpec.Utils
import QuickSpec.Type hiding (defaultTo)
import Data.Proxy
import Data.Word

-- | The entire QuickSpec configuration.
-- The only fields you will probably need are
-- `constants`, `instances`, `predicates` and `maxTermSize`.
--
-- As a simple example, the following signature explores @++@ and @reverse@:
--
-- @
-- sig =
--   `signature` {
--      `constants` = [
--        `constant` "reverse" (reverse :: [`A`] -> [`A`]),
--        `constant` "++" ((++) :: [`A`] -> [`A`] -> [`A`]) ]}
-- @
--
-- To test a user-defined datatype, use `baseType`:
--
-- @
-- data T = ...
-- sig =
--   `signature` {
--     `constants` = ...,
--     `instances` = [`baseType` (undefined :: T)] }
-- @
--
-- To test a /polymorphic/ user-defined datatype, you will need to use `inst` or
-- `makeInstance` to declare `Ord` and `Arbitrary` instances:
--
-- @
-- data T a = ...
-- sig =
--   `signature` {
--      `constants` = ...,
--      `instances` = [
--        `inst` (`Sub` `Dict` :: Ord `A` `:-` Ord (T `A`)),
--        `inst` (`Sub` `Dict` :: Arbitrary `A` `:-` Arbitrary (T `A`)) ]}
-- @
--
-- or:
--
-- @
-- data T a = ...
-- sig =
--   `signature` {
--      `constants` = ...,
--      `instances` = [
--        `makeInstance` (\(Dict :: Dict (Ord A) -> Dict :: Dict (Ord (T A)))),
--        `makeInstance` (\(Dict :: Dict (Arbitrary A) -> Dict :: Dict (Arbitrary (T A)))) ]}
-- @
--
-- Instead of an `Arbitrary` and `Ord` instance, it is possible to supply a
-- generator and an observational equality function; see @examples/PrettyPrinting.hs@.
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

-- | Declare a new monomorphic type.
baseType :: forall proxy a. (Ord a, Arbitrary a, Typeable a) => proxy a -> Sig
baseType _ =
  mconcat [
    inst (Dict :: Dict (Ord a)),
    inst (Dict :: Dict (Arbitrary a))]

-- | Declare a new monomorphic type, saying how you want variables of that type to be named.
baseTypeNames :: forall proxy a. (Ord a, Arbitrary a, Typeable a) => [String] -> proxy a -> Sig
baseTypeNames names proxy =
  baseType proxy `mappend` inst (Names names :: Names a)

inst :: Typeable a => a -> Sig
inst x =
  Sig (\_ -> modL Haskell.lens_instances (`mappend` Haskell.inst x))

appendAt :: Int -> a -> [[a]] -> [[a]]
appendAt n x [] = appendAt n x [[]]
appendAt 0 x (xs:xss) = (xs ++ [x]):xss
appendAt n x (xs:xss) = xs:appendAt (n-1) x xss

-- | Declare a constant with a given name and value.
-- If the constant you want to use is polymorphic, you can use the types
-- `A`, `B`, `C`, `D`, `E` to monomorphise it, for example:
--
-- > constant "reverse" (reverse :: [A] -> [A])
--
-- QuickSpec will then understand that the constant is really polymorphic.
con :: Typeable a => String -> a -> Sig
con name x =
  Sig (\n -> modL Haskell.lens_constants (appendAt n (Haskell.con name x)))

-- | Declare a predicate with a given name and value.
-- The predicate should have type @... -> Bool@.
predicate :: ( Predicateable a
             , Typeable a
             , Typeable (TestCase a))
             => String -> a -> Sig
predicate name x =
  Sig (\n -> modL Haskell.lens_predicates (appendAt n (Haskell.predicate name x)))

-- | Declare a part of a signature as consisting of background functions.
-- These will be explored separately before the rest of the functions.
--
-- XXX example
background :: Signature sig => sig -> Sig
background signature =
  Sig (\n -> sig (n+1))
  where
    Sig sig = toSig signature

-- | Run QuickCheck several times in succession, adding more functions each time.
--
-- XXX example geometry
series :: Signature sig => [sig] -> Sig
series = foldl op mempty . map toSig
  where
    op sigs sig = toSig [background sigs, sig]

-- | Set the number of test cases to try for each law (default: 1000).
withMaxTests :: Int -> Sig
withMaxTests n =
  Sig (\_ -> setL (QuickCheck.lens_num_tests # Haskell.lens_quickCheck) n)

-- | Set the maximum size of generated test data (default: 20).
withMaxTestSize :: Int -> Sig
withMaxTestSize n =
  Sig (\_ -> setL (QuickCheck.lens_max_test_size # Haskell.lens_quickCheck) n)

-- | Set a fixed seed
withFixedSeed :: (Word64, Word64, Word64, Word64) -> Sig
withFixedSeed s = Sig (\_ -> setL (QuickCheck.lens_fixed_seed # Haskell.lens_quickCheck) (Just . QCGen . seedTFGen $ s))

-- | Choose how hard QuickSpec tries to filter out redundant equations (default: no limit).
--
-- If you experience long pauses when running QuickSpec, try setting this number
-- to 2 or 3.
withPruningDepth :: Int -> Sig
withPruningDepth n =
  Sig (\_ -> setL (Twee.lens_max_cp_depth # Haskell.lens_twee) n)

-- | Set the maximum term size QuickSpec will consider when it filters out redundant equations (default: same as maximum term size).
withPruningTermSize :: Int -> Sig
withPruningTermSize n =
  Sig (\_ -> setL (Twee.lens_max_term_size # Haskell.lens_twee) n)

-- | Set the maximum size of terms to explore (default: 7).
withMaxTermSize :: Int -> Sig
withMaxTermSize n = Sig (\_ -> setL Haskell.lens_max_size n)

-- | Choose which type variables default to for testing.
defaultTo :: Typeable a => proxy a -> Sig
defaultTo proxy = Sig (\_ -> setL Haskell.lens_default_to (typeRep proxy))

-- | Run QuickSpec on a given signature.
quickSpec :: Signature sig => sig -> IO ()
quickSpec signature =
  Haskell.quickSpec (sig 0 Haskell.defaultConfig)
  where
    Sig sig = toSig signature
