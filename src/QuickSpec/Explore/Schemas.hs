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
import QuickSpec.Testing.DecisionTree hiding (Singleton)
import QuickSpec.Utils
import qualified QuickSpec.Explore.Terms as Terms
import QuickSpec.Explore.Terms(Result(..))
import Control.Monad.Trans.State.Strict hiding (State)
import Data.Typeable
import Data.List
import Data.Ord

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

-- The schema is represented as a term where there is only one distinct variable of each type
explore ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> State testcase result fun ->
  m (State testcase result fun, Maybe (Term fun))
explore t state@State{..} = do
  (classes, res) <- withReadOnlyPruner $ Terms.explore t st_classes
  let state' = state{st_classes = classes}
  case res of
    Singleton ->
      if st_instantiate_singleton t then
        instantiate t t state'
      else
        return (state', Just t)
    Discovered ([] :=>: _ :=: u) ->
      exploreIn u t state'
    Knew ([] :=>: _ :=: u) ->
      exploreIn u t state'
    _ -> error "term layer returned non-equational property"

exploreIn ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> Term fun -> State testcase result fun ->
  m (State testcase result fun, Maybe (Term fun))
exploreIn rep t state@State{..} =
  case Map.lookup rep st_instances of
    Nothing -> do
      -- First time instantiating this class - instantiate both terms
      (state, _) <- instantiate rep rep state
      (state, mt) <- instantiate rep t state
      return (state, mt)
    Just _ ->
      instantiate rep t state
    
instantiate ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> Term fun -> State testcase result fun ->
  m (State testcase result fun, Maybe (Term fun))
instantiate rep t state@State{..} = do
  let
    instances = sortBy (comparing generality) (allUnifications (mostGeneral t))
    loop [] terms =
      return
        (state{st_instances = Map.insert rep terms st_instances}, Just t)
    loop (t:ts) terms = do
      (terms, _) <- Terms.explore t terms
      loop ts terms
  
  let terms = Map.findWithDefault st_empty rep st_instances
  -- First check if schema is redundant
  (terms, res) <- Terms.explore (mostGeneral t) terms
  case res of
    Singleton -> loop instances terms
    _ ->
      return (state{st_instances = Map.insert rep terms st_instances}, Nothing)

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
