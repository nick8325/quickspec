-- Utilities for testing functions that return partial results.
{-# LANGUAGE Rank2Types #-}
module Test.QuickSpec.Approximate where

import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickSpec.Signature
import Test.QuickSpec.Term
import Test.QuickSpec.Utils
import Test.QuickSpec.Utils.Typeable
import Control.Monad
import Control.Monad.Reader
import Control.Spoon
import System.Random
import Data.Monoid

newtype Plug = Plug { unPlug :: forall a. Partial a => Gen a -> Gen a }
type GP = ReaderT Plug Gen

plug :: Partial a => GP a -> GP a
plug x = ReaderT (\plug -> unPlug plug (runReaderT x plug))

class (Typeable a, Arbitrary a, Eq a) => Partial a where
  unlifted :: a -> GP a
  unlifted x = return x

lifted :: Partial a => a -> GP a
lifted x = plug (unlifted x)

instance Partial ()
instance Partial Int
instance Partial Integer
instance Partial Bool

instance Partial a => Partial [a] where
  unlifted [] = return []
  unlifted (x:xs) = liftM2 (:) (lifted x) (lifted xs)

approximate :: Partial a => (StdGen, Int) -> a -> a
approximate (g, n) x = unGen (runReaderT (lifted x) (Plug plug)) g n
  where
    plug :: forall a. Partial a => Gen a -> Gen a
    plug x =
      sized $ \m ->
        if m == 0 then return (unGen arbitrary g n)
        else resize (m-1) $ do
          y <- x
          case spoony y of
            Just z -> return z
            Nothing -> return (unGen arbitrary g n)

pobserver :: (Ord a, Partial a) => a -> Sig
pobserver x = observerSig (Observer (PGen (return id) (MkGen f)))
  where f g n y = approximate (g, n `max` 50) (y `asTypeOf` x)

genPartial :: Partial a => a -> Gen a
genPartial x = runReaderT (lifted x) (Plug plug)
  where
    plug x = frequency [(1, undefined), (3, x)]

pvars :: (Ord a, Partial a) => [String] -> a -> Sig
pvars xs w =
  pobserver w
  `mappend` variableSig [ Variable (Atom (symbol x 0 w) (PGen g g')) | x <- xs ]
  `mappend` totalSig g
  `mappend` partialSig g'
  `mappend` typeSig w
  where
    g = arbitrary `asTypeOf` return w
    g' = g >>= genPartial