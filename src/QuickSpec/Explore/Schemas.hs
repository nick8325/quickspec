-- Theory exploration which works on a schema at a time.
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards, TupleSections, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-}
module QuickSpec.Explore.Schemas where

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Testing
import QuickSpec.Utils
import qualified QuickSpec.Explore.Terms as Terms
import QuickSpec.Explore.Terms(Terms)
import Control.Monad.Trans.State.Strict hiding (State)
import Data.List
import Data.Ord
import Data.Lens.Light
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Maybe
import Control.Monad

data Schemas testcase result schema norm =
  Schemas {
    sc_instantiate_singleton :: schema -> Bool,
    sc_empty :: Terms testcase result schema norm,
    sc_classes :: Terms testcase result schema norm,
    sc_instantiated :: Set schema,
    sc_instances :: Map schema (Terms testcase result schema norm) }

makeLensAs ''Schemas
  [("sc_classes", "classes"),
   ("sc_instances", "instances"),
   ("sc_instantiated", "instantiated")]

instance_ :: Ord schema => schema -> Lens (Schemas testcase result schema norm) (Terms testcase result schema norm)
instance_ t = reading (\Schemas{..} -> keyDefault t sc_empty # instances)

class Symbolic fun a => Schematic fun a where
  term :: a -> Term fun
  mostGeneralWith :: Ord b => (Type -> b) -> a -> a
  mostSpecific :: a -> a
  mostSpecific = subst (\(V ty _) -> Var (V ty 0))

mostGeneral :: Schematic fun a => a -> a
mostGeneral = mostGeneralWith id

instance Schematic fun (Term fun) where
  term = id
  mostGeneralWith = mostGeneralTerm

initialState ::
  (schema -> Bool) ->
  (schema -> testcase -> result) ->
  Schemas testcase result schema norm
initialState inst eval =
  Schemas {
    sc_instantiate_singleton = inst,
    sc_empty = Terms.initialState eval,
    sc_classes = Terms.initialState eval,
    sc_instantiated = Set.empty,
    sc_instances = Map.empty }

data Result schema =
    Accepted { result_props :: [Prop schema] }
  | Rejected { result_props :: [Prop schema] }

-- The schema is represented as a term where there is only one distinct variable of each type
explore ::
  (Ord result, Ord schema, Ord norm, Typed schema, Schematic fun schema,
  MonadTester testcase schema m, MonadPruner schema norm m) =>
  schema -> StateT (Schemas testcase result schema norm) m (Result schema)
explore t0 = do
  let t = mostSpecific t0
  res <- zoom classes (Terms.explore t)
  case res of
    Terms.Singleton -> do
      inst <- gets sc_instantiate_singleton
      if inst t then
        instantiateRep t
       else do
        -- Add the most general instance of the schema
        zoom (instance_ t) (Terms.explore (mostGeneral t))
        return (Accepted [])
    Terms.Discovered ([] :=>: _ :=: u) ->
      exploreIn u t
    Terms.Knew ([] :=>: _ :=: u) ->
      exploreIn u t
    _ -> error "term layer returned non-equational property"

{-# INLINEABLE exploreIn #-}
exploreIn ::
  (Ord result, Ord schema, Ord norm, Typed schema, Schematic fun schema,
  MonadTester testcase schema m, MonadPruner schema norm m) =>
  schema -> schema ->
  StateT (Schemas testcase result schema norm) m (Result schema)
exploreIn rep t = do
  -- First check if schema is redundant
  res <- zoom (instance_ rep) (Terms.explore (mostGeneral t))
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
  (Ord result, Ord schema, Ord norm, Typed schema, Schematic fun schema,
  MonadTester testcase schema m, MonadPruner schema norm m) =>
  schema ->
  StateT (Schemas testcase result schema norm) m (Result schema)
instantiateRep t = do
  instantiated %= Set.insert t
  instantiate t t

{-# INLINEABLE instantiate #-}
instantiate ::
  (Ord result, Ord schema, Ord norm, Typed schema, Schematic fun schema,
  MonadTester testcase schema m, MonadPruner schema norm m) =>
  schema -> schema ->
  StateT (Schemas testcase result schema norm) m (Result schema)
instantiate rep t = zoom (instance_ rep) $ do
  let instances = sortBy (comparing (generality . term)) (allUnifications (mostGeneral t))
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
mostGeneralTerm :: Ord a => (Type -> a) -> Term f -> Term f
mostGeneralTerm f s = evalState (aux s) Map.empty
  where
    aux (Var (V ty _)) = do
      m <- get
      let n = Map.findWithDefault 0 (f ty) m
      put $! Map.insert (f ty) (n+1) m
      return (Var (V ty n))
    aux (App f xs) = fmap (App f) (mapM aux xs)

allUnifications :: Schematic fun a => a -> [a]
allUnifications t = map f ss
  where
    vs = [ map (x,) (take (varCount x) xs) | xs <- partitionBy typ (usort (vars (term t))), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault undefined x s
    f s = subst (Var . go s) t
    varCount _ = 4
