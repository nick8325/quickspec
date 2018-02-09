-- Theory exploration which works on a schema at a time.
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards, TupleSections #-}
module QuickSpec.Explore.Schemas where

import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Testing
import QuickSpec.Utils
import qualified QuickSpec.Explore.Terms as Terms
import Control.Monad.Trans.State.Strict hiding (State)
import Data.Typeable
import Data.List
import Data.Ord
import Debug.Trace

data State testcase result fun =
  State {
    st_instantiate_singleton :: Term fun -> Bool,
    st_empty :: Terms.State testcase result (Term fun),
    st_classes :: Terms.State testcase result (Term fun),
    st_instances :: Map (Term fun) (Terms.State testcase result (Term fun)) }

initialState ::
  (Term fun -> Bool) ->
  (Term fun -> testcase -> result) ->
  State testcase result fun
initialState inst eval =
  State {
    st_instantiate_singleton = inst,
    st_empty = Terms.initialState eval,
    st_classes = Terms.initialState eval,
    st_instances = Map.empty }

data Result testcase result fun =
    Accepted { result_state :: State testcase result fun, result_props :: [Prop (Term fun)] }
  | Rejected { result_state :: State testcase result fun, result_props :: [Prop (Term fun)] }

-- The schema is represented as a term where there is only one distinct variable of each type
-- Discovered properties are added to the pruner. Use watchPruner to see them.
explore ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> State testcase result fun ->
  m (Result testcase result fun)
explore t state@State{..} = do
  (classes, res) <- Terms.explore t st_classes
  let state' = state{st_classes = classes}
  case res of
    Terms.Singleton ->
      if st_instantiate_singleton t then
        instantiate t t state'
      else -- XX this is wrong - should generate most general version only
        return (Accepted state' [])
    Terms.Discovered prop@([] :=>: _ :=: u) ->
      exploreIn u t state'
    Terms.Knew ([] :=>: _ :=: u) ->
      exploreIn u t state'
    _ -> error "term layer returned non-equational property"

{-# INLINEABLE exploreIn #-}
exploreIn ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> Term fun -> State testcase result fun ->
  m (Result testcase result fun)
exploreIn rep t state@State{..} =
  case Map.lookup rep st_instances of
    Nothing -> do
      -- First time instantiating this class - instantiate both terms

      -- rep must be accepted because the equivalence relation is empty,
      -- but it may generate properties where both sides have rep as schema
      Accepted state props <- instantiate rep rep state
      res <- instantiate rep t state
      return res { result_props = props ++ result_props res }
    Just _ ->
      instantiate rep t state
    
{-# INLINEABLE instantiate #-}
instantiate ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> Term fun -> State testcase result fun ->
  m (Result testcase result fun)
instantiate rep t state@State{..} = do
  let
    instances = sortBy (comparing generality) (allUnifications (mostGeneral t))
    loop [] terms props =
      return
        (Accepted state{st_instances = Map.insert rep terms st_instances} (reverse props))
    loop (t:ts) terms props = do
      (terms, res) <- Terms.explore t terms
      case res of
        Terms.Discovered prop -> do
          add prop
          loop ts terms (prop:props)
        _ -> loop ts terms props
  
  let terms = Map.findWithDefault st_empty rep st_instances
  -- First check if schema is redundant
  (terms, res) <- Terms.explore (mostGeneral t) terms
  case res of
    Terms.Singleton -> loop instances terms []
    Terms.Discovered prop -> do
      add prop
      return (Rejected state{st_instances = Map.insert rep terms st_instances} [prop])
    Terms.Knew _ ->
      return (Rejected state{st_instances = Map.insert rep terms st_instances} [])

-- sortBy (comparing generality) should give most general instances first.
generality :: Term f -> (Int, [Var])
generality t = (-length (usort (vars t)), vars t)

-- | Instantiate a schema by making all the variables different.
mostGeneral :: Term f -> Term f
mostGeneral s = evalState (aux s) Map.empty
  where
    aux (Var (V ty _)) = do
      m <- get
      let n = Map.findWithDefault 0 ty m
      put $! Map.insert ty (n+1) m
      return (Var (V ty n))
    aux (App f xs) = fmap (App f) (mapM aux xs)

allUnifications :: Term f -> [Term f]
allUnifications t = map f ss
  where
    vs = [ map (x,) (take (varCount x) xs) | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault undefined x s
    f s = subst (Var . go s) t
    varCount _ = 3
