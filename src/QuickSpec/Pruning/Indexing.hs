{-# LANGUAGE DeriveFunctor #-}
-- Term indexing (perfect discrimination trees).
-- Note: for efficiency, terms should be canonically alpha-renamed before
-- being inserted into the index.
module QuickSpec.Pruning.Indexing where

import QuickSpec.Base hiding (empty)
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Data.Rewriting.Substitution.Ops as Subst
import qualified Data.DList as DList
import Data.DList(DList)
import Data.Maybe
import Control.Applicative
import Control.Monad

data Index f v a =
  Index {
    here :: Set a,
    fun  :: Map f (Index f v a),
    var  :: Map v (Index f v a) } deriving Show

updateHere :: Ord a => (Set a -> Set a) -> Index f v a -> Index f v a
updateHere f idx = idx { here = f (here idx) }

updateFun :: (Ord f, Ord v) => f -> (Index f v a -> Index f v a) -> Index f v a -> Index f v a
updateFun x f idx =
  idx {
    fun = Map.insert x (f (Map.findWithDefault QuickSpec.Pruning.Indexing.empty x (fun idx))) (fun idx) }

updateVar :: (Ord f, Ord v) => v -> (Index f v a -> Index f v a) -> Index f v a -> Index f v a
updateVar x f idx =
  idx {
    var = Map.insert x (f (Map.findWithDefault QuickSpec.Pruning.Indexing.empty x (var idx))) (var idx) }

empty :: Index f v a
empty = Index Set.empty Map.empty Map.empty

insert :: (Ord f, Ord v, Ord a) => Tm f v -> a -> Index f v a -> Index f v a
insert t = insertFlat (symbols t)
  where
    insertFlat [] y idx = updateHere (Set.insert y) idx
    insertFlat (Left x:xs) y idx = updateFun x (insertFlat xs y) idx
    insertFlat (Right x:xs) y idx = updateVar x (insertFlat xs y) idx

delete :: (Ord f, Ord v, Ord a) => Tm f v -> a -> Index f v a -> Index f v a
delete t = deleteFlat (symbols t)
  where
    deleteFlat [] y idx = updateHere (Set.delete y) idx
    deleteFlat (Left x:xs) y idx = updateFun x (deleteFlat xs y) idx
    deleteFlat (Right x:xs) y idx = updateVar x (deleteFlat xs y) idx

data Result f v a =
  Result {
    result :: a,
    subst :: Subst f v }
  deriving (Functor, Show)

newtype Results f v a =
  Results {
    unResults :: DList (Result f v a) }
  deriving (Functor, Show)

instance (Ord f, Ord v) => Applicative (Results f v) where
  pure = return
  (<*>) = liftM2 ($)

instance (Ord f, Ord v) => Monad (Results f v) where
  return x = Results (return (Result x (Subst.fromMap Map.empty)))
  Results xs >>= f =
    Results $ do
      Result x sub1 <- xs
      Result y sub2 <- unResults (f x)
      Just sub <- return (Subst.merge sub1 sub2)
      return (Result y sub)

instance (Ord f, Ord v) => Alternative (Results f v) where
  empty = mzero
  (<|>) = mplus

instance (Ord f, Ord v) => MonadPlus (Results f v) where
  mzero = Results mzero
  Results x `mplus` Results y = Results (x `mplus` y)

lookup :: (Ord f, Ord v) => Tm f v -> Index f v a -> [Result f v a]
lookup t idx =
  concatMap flattenResult (DList.toList (unResults (lookupPartial t idx)))
  where
    flattenResult (Result idx' sub) =
      [ Result m sub | m <- Set.toList (here idx') ]

lookupPartial, lookupVar, lookupFun ::
  (Ord f, Ord v) => Tm f v -> Index f v a -> Results f v (Index f v a)
lookupPartial t idx = lookupVar t idx `mplus` lookupFun t idx

lookupVar t idx =
  Results $ do
    (x, idx') <- DList.fromList (Map.toList (var idx))
    return (Result idx' (Subst.fromMap (Map.singleton x t)))

lookupFun (Fun f ts) idx =
  case Map.lookup f (fun idx) of
    Nothing -> mzero
    Just idx' -> foldr (>=>) return (map lookupPartial ts) idx'
lookupFun _ _ = mzero

elems :: Index f v a -> [a]
elems idx = DList.toList (aux idx)
  where
    aux idx =
      DList.fromList (Set.toList (here idx)) `mplus`
      msum (map aux (Map.elems (fun idx))) `mplus`
      msum (map aux (Map.elems (var idx)))
