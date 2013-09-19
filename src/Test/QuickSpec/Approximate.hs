-- Utilities for testing functions that return partial results.
{-# LANGUAGE Rank2Types #-}
module Test.QuickSpec.Approximate where

import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
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

approximate :: Partial a => (forall a. Partial a => a -> Maybe a) -> QCGen -> Int -> a -> a
approximate eval g n x = unGen (runReaderT (lifted x) (Plug plug)) g n
  where
    plug :: forall a. Partial a => Gen a -> Gen a
    plug x =
      sized $ \m ->
        if m == 0 then return (unGen arbitrary g 10)
        else resize (m-1) $ do
          y <- x
          case eval y of
            Just z -> return z
            Nothing -> return (unGen arbitrary g 10)

pobserver :: (Ord a, Partial a) => a -> Sig
pobserver x = observerSig (Observer (PGen (MkGen tot) (MkGen part)))
  where tot g n y = approximate Just g n (y `asTypeOf` x)
        part g n y = approximate spoony g n (y `asTypeOf` x)

genPartial :: Partial a => a -> Gen a
genPartial x = runReaderT (lifted x) (Plug plug)
  where
    plug x = frequency [(1, undefined), (3, x)]

pvars :: (Ord a, Partial a) => [String] -> a -> Sig
pvars xs w = pobserver w `mappend` primVars0 0 xs (PGen g g')
  where
    g = arbitrary `asTypeOf` return w
    g' = g >>= genPartial
