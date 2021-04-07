-- Theory exploration which works on a schema at a time.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, PatternGuards, TupleSections, MultiParamTypeClasses, FlexibleInstances #-}
module QuickSpec.Internal.Explore.Schemas where

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Utils
import QuickSpec.Internal.Terminal
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

-- | Constrains how variables of a particular type may occur in a term.
data VariableUse =
    UpTo Int -- ^ @UpTo n@: terms may contain up to @n@ distinct variables of this type
             -- (in some cases, laws with more variables may still be found)
  | Linear   -- ^ Each variable in the term must be distinct
  deriving (Eq, Show)

data Schemas testcase result fun norm =
  Schemas {
    sc_use :: Type -> VariableUse,
    sc_instantiate_singleton :: Term fun -> Bool,
    sc_empty :: Terms testcase result (Term fun) norm,
    sc_classes :: Terms testcase result (Term fun) norm,
    sc_instantiated :: Set (Term fun),
    sc_instances :: Map (Term fun) (Terms testcase result (Term fun) norm) }

classes = lens sc_classes (\x y -> y { sc_classes = x })
use = lens sc_use (\x y -> y { sc_use = x })
instances = lens sc_instances (\x y -> y { sc_instances = x })
instantiated = lens sc_instantiated (\x y -> y { sc_instantiated = x })

instance_ :: Ord fun => Term fun -> Lens (Schemas testcase result fun norm) (Terms testcase result (Term fun) norm)
instance_ t = reading (\Schemas{..} -> keyDefault t sc_empty # instances)

initialState ::
  (Type -> VariableUse) ->
  (Term fun -> Bool) ->
  (Term fun -> testcase -> result) ->
  Schemas testcase result fun norm
initialState use inst eval =
  Schemas {
    sc_use = use,
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
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m, MonadTerminal m) =>
  Term fun -> StateT (Schemas testcase result fun norm) m (Result fun)
explore t0 = do
  use <- access use
  if or [use ty == UpTo 0 | ty <- usort (map typ (vars t0))] then return (Rejected []) else do
    let t = mostSpecific t0
    res <- zoom classes (Terms.explore t)
    case res of
      Terms.Singleton -> do
        inst <- gets sc_instantiate_singleton
        if inst t then
          instantiateRep t
         else do
          -- Add the most general instance of the schema
          zoom (instance_ t) (Terms.explore (mostGeneral use t0))
          return (Accepted [])
      Terms.Discovered ([] :=>: _ :=: u) ->
        exploreIn u t
      Terms.Knew ([] :=>: _ :=: u) ->
        exploreIn u t
      _ -> error "term layer returned non-equational property"

{-# INLINEABLE exploreIn #-}
exploreIn ::
  (PrettyTerm fun, Ord result, Ord fun, Ord norm, Typed fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m, MonadTerminal m) =>
  Term fun -> Term fun ->
  StateT (Schemas testcase result fun norm) m (Result fun)
exploreIn rep t = do
  -- First check if schema is redundant
  use <- access use
  res <- zoom (instance_ rep) (Terms.explore (mostGeneral use t))
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
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m, MonadTerminal m) =>
  Term fun ->
  StateT (Schemas testcase result fun norm) m (Result fun)
instantiateRep t = do
  instantiated %= Set.insert t
  instantiate t t

{-# INLINEABLE instantiate #-}
instantiate ::
  (PrettyTerm fun, Ord result, Ord fun, Ord norm, Typed fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m, MonadTerminal m) =>
  Term fun -> Term fun ->
  StateT (Schemas testcase result fun norm) m (Result fun)
instantiate rep t = do
  use <- access use
  zoom (instance_ rep) $ do
    let instances = sortBy (comparing generality) (allUnifications use (mostGeneral use t))
    Accepted <$> catMaybes <$> forM instances (\t -> do
      res <- Terms.explore t
      case res of
        Terms.Discovered prop -> do
          res <- add prop
          if res then return (Just prop) else return Nothing
        _ -> return Nothing)

-- sortBy (comparing generality) should give most general instances first.
generality :: Term f -> (Int, [Var])
generality t = (-length (usort (vars t)), vars t)

mkVar :: Type -> Int -> Var
mkVar ty n = V ty m
  -- Try to make sure that variables of different types don't end up with the
  -- same number. It would be better to deal with this in QuickSpec.Term.
  -- (Note: the problem we are trying to avoid is that, if two variables have
  -- the same number and different but unifiable types, then a type substitution
  -- can turn them into the same variable.)
  where
    m = fromIntegral (labelNum (label (ty, n)))

-- | Instantiate a schema by making all the variables different.
mostGeneral :: (Type -> VariableUse) -> Term f -> Term f
mostGeneral use s = evalState (aux s) Map.empty
  where
    aux (Var (V ty _)) = do
      m <- get
      let n :: Int
          n = Map.findWithDefault 0 ty m
      unless (use ty == UpTo 1) $
        put $! Map.insert ty (n+1) m
      return (Var (mkVar ty n))
    aux (Fun f) = return (Fun f)
    aux (t :$: u) = liftM2 (:$:) (aux t) (aux u)

mostSpecific :: Term f -> Term f
mostSpecific = subst (\(V ty _) -> Var (mkVar ty 0))

allUnifications :: (Type -> VariableUse) -> Term fun -> [Term fun]
allUnifications use t =
  [ subst (\x -> Var (Map.findWithDefault undefined x s)) t | s <- ss ]
  where
    ss =
      map Map.fromList $ map concat $ sequence
        [substsFor xs (typ y) | xs@(y:_) <- partitionBy typ (usort (vars t))]

    substsFor xs ty =
      case use ty of
        UpTo k ->
          sequence [[(x, v) | v <- take k vs] | x <- xs]
        Linear ->
          map (zip xs) (permutations (take (length xs) vs))
      where
        vs = map (mkVar ty) [0..]
