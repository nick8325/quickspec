-- Theory exploration which works on a schema at a time.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards, TupleSections, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-}
module QuickSpec.Internal.Explore.Schemas where

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Utils
import qualified QuickSpec.Internal.Explore.Terms as Terms
import QuickSpec.Internal.Explore.Terms(Terms)
import Control.Monad.Trans.State.Strict hiding (State)
import Data.List
import Data.Ord
import Data.Lens.Light
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Maybe
import Control.Monad
import Twee.Label

data Schemas testcase result fun norm =
  Schemas {
    sc_single_use :: Type -> Bool,
    sc_instantiate_singleton :: Term fun -> Bool,
    sc_empty :: Terms testcase result (Term fun) norm,
    sc_classes :: Terms testcase result (Term fun) norm,
    sc_instantiated :: Set (Term fun),
    sc_instances :: Map (Term fun) (Terms testcase result (Term fun) norm) }

makeLensAs ''Schemas
  [("sc_classes", "classes"),
   ("sc_single_use", "single_use"),
   ("sc_instances", "instances"),
   ("sc_instantiated", "instantiated")]

instance_ :: Ord fun => Term fun -> Lens (Schemas testcase result fun norm) (Terms testcase result (Term fun) norm)
instance_ t = reading (\Schemas{..} -> keyDefault t sc_empty # instances)

initialState ::
  (Type -> Bool) ->
  (Term fun -> Bool) ->
  (Term fun -> testcase -> result) ->
  Schemas testcase result fun norm
initialState singleUse inst eval =
  Schemas {
    sc_single_use = singleUse,
    sc_instantiate_singleton = inst,
    sc_empty = Terms.initialState eval,
    sc_classes = Terms.initialState eval,
    sc_instantiated = Set.empty,
    sc_instances = Map.empty }

data Result fun =
    Accepted { result_props :: [Prop (Term fun)] }
  | Rejected { result_props :: [Prop (Term fun)] }

-- The schema is represented as a term where there is only one distinct variable of each type
explore ::
  (PrettyTerm fun, Ord result, Ord fun, Ord norm, Typed fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m) =>
  Term fun -> StateT (Schemas testcase result fun norm) m (Result fun)
explore t0 = do
  let t = mostSpecific t0
  res <- zoom classes (Terms.explore t)
  singleUse <- access single_use
  case res of
    Terms.Singleton -> do
      inst <- gets sc_instantiate_singleton
      if inst t then
        instantiateRep t
       else do
        -- Add the most general instance of the schema
        zoom (instance_ t) (Terms.explore (mostGeneral singleUse t0))
        return (Accepted [])
    Terms.Discovered ([] :=>: _ :=: u) ->
      exploreIn u t
    Terms.Knew ([] :=>: _ :=: u) ->
      exploreIn u t
    _ -> error "term layer returned non-equational property"

{-# INLINEABLE exploreIn #-}
exploreIn ::
  (PrettyTerm fun, Ord result, Ord fun, Ord norm, Typed fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m) =>
  Term fun -> Term fun ->
  StateT (Schemas testcase result fun norm) m (Result fun)
exploreIn rep t = do
  -- First check if schema is redundant
  singleUse <- access single_use
  res <- zoom (instance_ rep) (Terms.explore (mostGeneral singleUse t))
  case res of
    Terms.Discovered prop -> do
      add prop
      return (Rejected [prop])
    Terms.Knew _ ->
      return (Rejected [])
    Terms.Singleton -> do
      -- Instantiate rep too if not already done
      inst <- access instantiated
      props <-
        if Set.notMember rep inst
        then result_props <$> instantiateRep rep
        else return []
      res <- instantiate rep t
      return res { result_props = props ++ result_props res }

{-# INLINEABLE instantiateRep #-}
instantiateRep ::
  (PrettyTerm fun, Ord result, Ord fun, Ord norm, Typed fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m) =>
  Term fun ->
  StateT (Schemas testcase result fun norm) m (Result fun)
instantiateRep t = do
  instantiated %= Set.insert t
  instantiate t t

{-# INLINEABLE instantiate #-}
instantiate ::
  (PrettyTerm fun, Ord result, Ord fun, Ord norm, Typed fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m) =>
  Term fun -> Term fun ->
  StateT (Schemas testcase result fun norm) m (Result fun)
instantiate rep t = do
  singleUse <- access single_use
  zoom (instance_ rep) $ do
    let instances = sortBy (comparing generality) (allUnifications singleUse (mostGeneral singleUse t))
    Accepted <$> catMaybes <$> forM instances (\t -> do
      res <- Terms.explore t
      case res of
        Terms.Discovered prop -> do
          add prop
          return (Just prop)
        _ -> return Nothing)

-- sortBy (comparing generality) should give most general instances first.
generality :: Term f -> (Int, [Var])
generality t = (-length (usort (vars t)), vars t)

-- | Instantiate a schema by making all the variables different.
mostGeneral :: (Type -> Bool) -> Term f -> Term f
mostGeneral singleUse s = evalState (aux s) Map.empty
  where
    aux (Var (V ty _)) = do
      m <- get
      let n :: Int
          n = Map.findWithDefault 0 ty m
      unless (singleUse ty) $
        put $! Map.insert ty (n+1) m
      let m = fromIntegral (labelNum (label (ty, n)))
      return (Var (V ty m))
    aux (App f xs) = fmap (App f) (mapM aux xs)

mostSpecific :: Term f -> Term f
mostSpecific = subst (\(V ty _) -> Var (V ty 0))

allUnifications :: (Type -> Bool) -> Term fun -> [Term fun]
allUnifications singleUse t = map f ss
  where
    vs = [ map (x,) (select xs) | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault undefined x s
    f s = subst (Var . go s) t
    select [V ty x] | not (singleUse ty) = [V ty x, V ty (succ x)]
    select xs = take 4 xs
