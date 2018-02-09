-- Theory exploration which works on a schema at a time.
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards, TupleSections, TemplateHaskell #-}
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
import Debug.Trace

data Schemas testcase result fun =
  Schemas {
    sc_instantiate_singleton :: Term fun -> Bool,
    sc_empty :: Terms testcase result (Term fun),
    sc_classes :: Terms testcase result (Term fun),
    sc_instances :: Map (Term fun) (Terms testcase result (Term fun)) }

makeLensAs ''Schemas [("sc_classes", "classes"), ("sc_instances", "instances")]

maybeInstance :: Ord fun => Term fun -> Lens (Schemas testcase result fun) (Maybe (Terms testcase result (Term fun)))
maybeInstance t = key t # instances

instance_ :: Ord fun => Term fun -> Lens (Schemas testcase result fun) (Terms testcase result (Term fun))
instance_ t =
  lens
    (\s@Schemas{..} -> Map.findWithDefault sc_empty t sc_instances)
    (\x s -> modL instances (Map.insert t x) s)

initialState ::
  (Term fun -> Bool) ->
  (Term fun -> testcase -> result) ->
  Schemas testcase result fun
initialState inst eval =
  Schemas {
    sc_instantiate_singleton = inst,
    sc_empty = Terms.initialState eval,
    sc_classes = Terms.initialState eval,
    sc_instances = Map.empty }

data Result fun =
    Accepted { result_props :: [Prop (Term fun)] }
  | Rejected { result_props :: [Prop (Term fun)] }

-- The schema is represented as a term where there is only one distinct variable of each type
-- Discovered properties are added to the pruner. Use watchPruner to see them.
explore ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> StateT (Schemas testcase result fun) m (Result fun)
explore t = do
  res <- zoom classes (Terms.explore t)
  case res of
    Terms.Singleton -> do
      inst <- gets sc_instantiate_singleton
      if inst t then
        instantiate t t
       else -- XX this is wrong - should generate most general version only
        return (Accepted [])
    Terms.Discovered ([] :=>: _ :=: u) ->
      exploreIn u t
    Terms.Knew ([] :=>: _ :=: u) ->
      exploreIn u t
    _ -> error "term layer returned non-equational property"

{-# INLINEABLE exploreIn #-}
exploreIn ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> Term fun ->
  StateT (Schemas testcase result fun) m (Result fun)
exploreIn rep t = do
  terms <- access (maybeInstance rep)
  case terms of
    Nothing -> do
      -- First time instantiating this class - instantiate both terms

      -- rep must be accepted because the equivalence relation is empty,
      -- but it may generate properties where both sides have rep as schema
      Accepted props <- instantiate rep rep
      res <- instantiate rep t
      return res { result_props = props ++ result_props res }
    Just _ ->
      instantiate rep t
    
{-# INLINEABLE instantiate #-}
instantiate ::
  (Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun -> Term fun ->
  StateT (Schemas testcase result fun) m (Result fun)
instantiate rep t = zoom (instance_ rep) $ do
  let
    instances = sortBy (comparing generality) (allUnifications (mostGeneral t))
    loop [] props = return (Accepted (reverse props))
    loop (t:ts) props = do
      res <- Terms.explore t
      case res of
        Terms.Discovered prop -> do
          add prop
          loop ts (prop:props)
        _ -> loop ts props

  -- First check if schema is redundant
  res <- Terms.explore (mostGeneral t)
  case res of
    Terms.Singleton -> trace ("instantiate " ++ prettyShow t) $ loop instances []
    Terms.Discovered prop -> do
      add prop
      return (Rejected [prop])
    Terms.Knew _ ->
      return (Rejected [])

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
