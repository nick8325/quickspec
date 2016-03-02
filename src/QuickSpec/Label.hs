-- | Assignment of unique IDs to values.
-- Inspired by the 'intern' package.

{-# LANGUAGE RecordWildCards, ScopedTypeVariables #-}
module QuickSpec.Label where

import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict(IntMap)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)

class Ord a => Labelled a where
  cache :: Cache a
  initialId :: a -> Int
  initialId _ = 0

type Cache a = IORef (CacheState a)
data CacheState a =
  CacheState {
    nextId :: {-# UNPACK #-} !Int,
    to     :: !(IntMap a),
    from   :: !(Map a Int) }
  deriving Show

mkCache :: forall a. Labelled a => Cache a
mkCache = unsafePerformIO (newIORef (CacheState (initialId (undefined :: a)) IntMap.empty Map.empty))

label :: Labelled a => a -> Int
label x =
  compare x x `seq`
  unsafeDupablePerformIO $
    atomicModifyIORef' cache $ \cache@CacheState{..} ->
      case Map.lookup x from of
        Nothing ->
          (CacheState
             (nextId+1)
             (IntMap.insert nextId x to)
             (Map.insert x nextId from),
           nextId)
        Just n -> (cache, n)

find :: Labelled a => Int -> Maybe a
find n =
  unsafeDupablePerformIO $ do
    CacheState{..} <- readIORef cache
    return (IntMap.lookup n to)
