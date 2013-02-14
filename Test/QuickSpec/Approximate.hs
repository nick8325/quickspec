-- Utilities for testing functions that return partial results.
{-# LANGUAGE Rank2Types #-}
module Test.QuickSpec.Approximate where

import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils
import Test.QuickSpec.Utils.Typeable
import Control.Monad
import Control.Monad.Reader
import Control.Spoon
import System.Random
import Data.Monoid

newtype Plug = Plug { unPlug :: forall a. Partial a => a -> Gen a }
type GP = ReaderT Plug Gen

plug :: Partial a => a -> GP a
plug x = do
  f <- ask
  ReaderT (\_ -> unPlug f x)

class (Typeable a, Arbitrary a, Eq a) => Partial a where
  unlifted :: a -> GP a
  unlifted x = return x

lifted :: Partial a => a -> GP a
lifted x = unlifted x >>= plug

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
    plug :: forall a. Partial a => a -> Gen a
    plug x =
      case spoony x of
        Nothing -> return (unGen arbitrary g n)
        Just y -> return y

pobserver :: (Ord a, Partial a) => a -> Sig
pobserver x = observerSig (Observer (MkGen f))
  where f g n y = approximate (g, n `max` 50) (y `asTypeOf` x)

genPartial :: Partial a => a -> Gen a
genPartial x = runReaderT (lifted x) (Plug plug)
  where
    plug x = frequency [(1, undefined), (3, return x)]

pvars :: (Ord a, Partial a) => [String] -> a -> Sig
pvars xs w = 
  pobserver w
  `mappend` gvars xs ((arbitrary `asTypeOf` return w) >>= genPartial)
