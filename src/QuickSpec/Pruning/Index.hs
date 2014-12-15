{-# LANGUAGE DeriveFunctor, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
-- Term indexing (perfect discrimination trees).
module QuickSpec.Pruning.Index where

import QuickSpec.Base hiding (empty)
import Control.Applicative
import Control.Monad
import qualified Data.DList as DList
import Data.DList(DList)
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Rewriting.Substitution.Ops as Subst
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Data.Set as Set
import Data.Set(Set)

data Index a =
  Index {
    here :: Set a,
    fun  :: Map (ConstantOf a) (Index a),
    var  :: Map (VariableOf a) (Index a) }
deriving instance (Show a, Show (ConstantOf a), Show (VariableOf a)) => Show (Index a)

updateHere :: Ord a => (Set a -> Set a) -> Index a -> Index a
updateHere f idx = idx { here = f (here idx) }

updateFun ::
  Ord (ConstantOf a) =>
  ConstantOf a -> (Index a -> Index a) -> Index a -> Index a
updateFun x f idx
  | QuickSpec.Pruning.Index.null idx' = idx { fun = Map.delete x (fun idx) }
  | otherwise = idx { fun = Map.insert x idx' (fun idx) }
  where
    idx' = f (Map.findWithDefault QuickSpec.Pruning.Index.empty x (fun idx))

updateVar ::
  Ord (VariableOf a) =>
  VariableOf a -> (Index a -> Index a) -> Index a -> Index a
updateVar x f idx
  | QuickSpec.Pruning.Index.null idx' = idx { var = Map.delete x (var idx) }
  | otherwise = idx { var = Map.insert x idx' (var idx) }
  where
    idx' = f (Map.findWithDefault QuickSpec.Pruning.Index.empty x (var idx))

empty :: Index a
empty = Index Set.empty Map.empty Map.empty

null :: Index a -> Bool
null idx = Set.null (here idx) && Map.null (fun idx) && Map.null (var idx)

mapMonotonic ::
  (a -> b) ->
  (ConstantOf a -> ConstantOf b) ->
  (VariableOf a -> VariableOf b) ->
  Index a -> Index b
mapMonotonic f g h (Index here fun var) =
  Index
    (Set.mapMonotonic f here)
    (fmap (mapMonotonic f g h) (Map.mapKeysMonotonic g fun))
    (fmap (mapMonotonic f g h) (Map.mapKeysMonotonic h var))

insert ::
  (Symbolic a, Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a), Ord a) =>
  a -> Index a -> Index a
insert t = insertFlat (symbols (term u))
  where
    u = canonicalise t
    insertFlat [] = updateHere (Set.insert u)
    insertFlat (Left x:xs) = updateFun x (insertFlat xs)
    insertFlat (Right x:xs) = updateVar x (insertFlat xs)

delete ::
  (Symbolic a, Ord (ConstantOf a), Ord (VariableOf a), Numbered (VariableOf a), Ord a) =>
  a -> Index a -> Index a
delete t = deleteFlat (symbols (term u))
  where
    u = canonicalise t
    deleteFlat [] = updateHere (Set.delete u)
    deleteFlat (Left x:xs) = updateFun x (deleteFlat xs)
    deleteFlat (Right x:xs) = updateVar x (deleteFlat xs)

data Result f v a =
  Result {
    result :: a,
    substitution :: Subst f v }
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

lookup ::
  (Symbolic a, Ord (ConstantOf a), Ord (VariableOf a)) =>
  TmOf a -> Index a -> [a]
lookup t idx =
  concatMap flattenResult (DList.toList (unResults (lookupPartial t idx)))
  where
    flattenResult (Result idx' sub) =
      [ substf (evalSubst sub) m | m <- Set.toList (here idx') ]

lookupPartial, lookupVar, lookupFun ::
  (Ord (ConstantOf a), Ord (VariableOf a)) =>
  TmOf a -> Index a -> Results (ConstantOf a) (VariableOf a) (Index a)
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

elems :: Index a -> [a]
elems idx = DList.toList (aux idx)
  where
    aux idx =
      DList.fromList (Set.toList (here idx)) `mplus`
      msum (map aux (Map.elems (fun idx))) `mplus`
      msum (map aux (Map.elems (var idx)))
