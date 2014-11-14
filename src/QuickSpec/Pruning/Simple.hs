module QuickSpec.Pruning.Simple where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Prop
import QuickSpec.Pruning
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Maybe

newtype SimplePruner = S [PropOf PruningTerm]

instance Pruner SimplePruner where
  emptyPruner _ = S []
  untypedAxiom  = simpleUnify
  untypedRep _  = simpleRep

modifyS f = modify (\(S x) -> S (f x))

simpleAreEqual :: Monad m => PropOf PruningTerm -> StateT SimplePruner m (Maybe PruningTerm)
simpleAreEqual (lhs :=>: t :=: u)
  | Measure (fromPruningTerm t) <= Measure (fromPruningTerm u) = do
    S eqs <- get
    return (simplifies (map unitProp lhs ++ eqs) u)
  | otherwise =
    simpleAreEqual (lhs :=>: u :=: t)
simpleAreEqual _ = return Nothing

simpleUnify :: Monad m => PropOf PruningTerm -> StateT SimplePruner m ()
simpleUnify prop@(lhs :=>: t :=: u) = do
  res <- simpleAreEqual prop
  case res of
    Just v |
      fromPruningTerm v `alwaysSimplerThan` fromPruningTerm t ||
      fromPruningTerm v `alwaysSimplerThan` fromPruningTerm u ->
        return ()
    _ ->
      modifyS (prop:)
simpleUnify prop = modifyS (prop:)

alwaysSimplerThan :: Term -> Term -> Bool
t `alwaysSimplerThan` u =
  size t <= size u &&
  Measure (schema t) < Measure (schema u) &&
  and [ sizeOk v | v <- vars t, v `elem` vars u ]
  where
    sizeOk v = occ v t <= occ v u
    occ v t = length [ v' | v' <- vars t, v == v' ]

simpleRep :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT SimplePruner m (Maybe PruningTerm)
simpleRep axioms t = do
  S eqs <- get
  return (simplifies (axioms++eqs) t)

simplifies :: [PropOf PruningTerm] -> PruningTerm -> Maybe PruningTerm
simplifies eqs t =
  msum [ simplifies1 u v t `mplus` simplifies1 v u t | [] :=>: u :=: v <- eqs ] `mplus`
  simplifiesThere eqs t
simplifiesThere eqs (Fun f ts) =
  fmap (Fun f) (simplifiesList eqs ts)
simplifiesThere _ _ = Nothing
simplifiesList eqs [] = Nothing
simplifiesList eqs (t:ts) = fmap (:ts) (simplifies eqs t) `mplus` fmap (t:) (simplifiesList eqs ts)

simplifies1 :: PruningTerm -> PruningTerm -> PruningTerm -> Maybe PruningTerm
simplifies1 t u v = do
  s <- match t v
  let w = subst s u
  guard (Measure (fromPruningTerm w) < Measure (fromPruningTerm v))
  return w
