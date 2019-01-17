-- | Miscellaneous utility functions.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE CPP #-}
module QuickSpec.Internal.Utils where

import Control.Arrow((&&&))
import Control.Exception
import Control.Spoon
import Data.List(groupBy, sortBy)
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif
import Data.Ord(comparing)
import System.IO
import qualified Control.Category as Category
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Language.Haskell.TH.Syntax
import Data.Lens.Light
import Twee.Base hiding (lookup)
import Control.Monad.Trans.State.Strict
import Control.Monad

(#) :: Category.Category cat => cat b c -> cat a b -> cat a c
(#) = (Category..)

key :: Ord a => a -> Lens (Map a b) (Maybe b)
key x = lens (Map.lookup x) (\my m -> Map.alter (const my) x m)

keyDefault :: Ord a => a -> b -> Lens (Map a b) b
keyDefault x y = lens (Map.findWithDefault y x) (\y m -> Map.insert x y m)

reading :: (a -> Lens a b) -> Lens a b
reading f = lens (\x -> getL (f x) x) (\y x -> setL (f x) y x)

fstLens :: Lens (a, b) a
fstLens = lens fst (\x (_, y) -> (x, y))

sndLens :: Lens (a, b) b
sndLens = lens snd (\y (x, _) -> (x, y))

makeLensAs :: Name -> [(String, String)] -> Q [Dec]
makeLensAs ty names =
  nameMakeLens ty (\x -> lookup x names)

repeatM :: Monad m => m a -> m [a]
repeatM = sequence . repeat

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value =
  map (map fst) .
  groupBy (\x y -> snd x == snd y) .
  sortBy (comparing snd) .
  map (id &&& value)

collate :: Ord a => ([b] -> c) -> [(a, b)] -> [(a, c)]
collate f = map g . partitionBy fst
  where
    g xs = (fst (head xs), f (map snd xs))

isSorted :: Ord a => [a] -> Bool
isSorted xs = and (zipWith (<=) xs (tail xs))

isSortedBy :: Ord b => (a -> b) -> [a] -> Bool
isSortedBy f xs = isSorted (map f xs)

usort :: Ord a => [a] -> [a]
usort = usortBy compare

usortBy :: (a -> a -> Ordering) -> [a] -> [a]
usortBy f = map head . groupBy (\x y -> f x y == EQ) . sortBy f

sortBy' :: Ord b => (a -> b) -> [a] -> [a]
sortBy' f = map snd . sortBy (comparing fst) . map (\x -> (f x, x))

usortBy' :: Ord b => (a -> b) -> [a] -> [a]
usortBy' f = map snd . usortBy (comparing fst) . map (\x -> (f x, x))

orElse :: Ordering -> Ordering -> Ordering
EQ `orElse` x = x
x  `orElse` _ = x

unbuffered :: IO a -> IO a
unbuffered x = do
  buf <- hGetBuffering stdout
  bracket_
    (hSetBuffering stdout NoBuffering)
    (hSetBuffering stdout buf)
    x

spoony :: Eq a => a -> Maybe a
spoony x = teaspoon ((x == x) `seq` x)

labelM :: Monad m => (a -> m b) -> [a] -> m [(a, b)]
labelM f = mapM (\x -> do { y <- f x; return (x, y) })

#if __GLASGOW_HASKELL__ < 710
isSubsequenceOf :: Ord a => [a] -> [a] -> Bool
[] `isSubsequenceOf` ys = True
(x:xs) `isSubsequenceOf` [] = False
(x:xs) `isSubsequenceOf` (y:ys)
  | x == y = xs `isSubsequenceOf` ys
  | otherwise = (x:xs) `isSubsequenceOf` ys
#endif

appendAt :: Int -> [a] -> [[a]] -> [[a]]
appendAt n xs [] = appendAt n xs [[]]
appendAt 0 xs (ys:yss) = (ys ++ xs):yss
appendAt n xs (ys:yss) = ys:appendAt (n-1) xs yss

-- Should be in Twee.Base.
antiunify :: Ord f => Term f -> Term f -> Term f
antiunify t u =
  build $ evalState (loop t u) (succ (snd (bound t) `max` snd (bound u)), Map.empty)
  where
    loop (App f ts) (App g us)
      | f == g =
        app f <$> zipWithM loop (unpack ts) (unpack us)
    loop (Var x) (Var y)
      | x == y =
        return (var x)
    loop t u = do
      (next, m) <- get
      case Map.lookup (t, u) m of
        Just v -> return (var v)
        Nothing -> do
          put (succ next, Map.insert (t, u) next m)
          return (var next)

{-# INLINE fixpoint #-}
fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x = fxp x
  where
    fxp x
      | x == y = x
      | otherwise = fxp y
      where
        y = f x
