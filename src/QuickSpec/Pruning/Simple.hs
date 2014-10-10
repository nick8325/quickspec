module QuickSpec.Pruning.Simple where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Pruning
import Control.Monad
import Control.Monad.Trans.State.Strict

newtype SimplePruner = S [(PruningTerm, PruningTerm)]

instance Pruner SimplePruner where
  untypedEmptyPruner = S []
  unifyUntyped = simpleUnify
  repUntyped = simpleRep

simpleUnify :: PruningTerm -> PruningTerm -> State SimplePruner Bool
simpleUnify t u
  | measure (fromPruningTerm t) < measure (fromPruningTerm u) = simpleUnify u t
simpleUnify u t = do
  S eqs <- get
  case simplifies eqs u of
    Just v -> do
      unless (fromPruningTerm v `alwaysSimplerThan` fromPruningTerm t ||
              fromPruningTerm v `alwaysSimplerThan` fromPruningTerm u)
        (put (S ((u,t):eqs)))
      return True
    Nothing -> do
      put (S ((u,t):eqs))
      return False

alwaysSimplerThan :: Term -> Term -> Bool
t `alwaysSimplerThan` u =
  size t <= size u &&
  and [ sizeOk v | v <- vars t, v `elem` vars u ]
  where
    sizeOk v = occ v t <= occ v u
    occ v t = length [ v' | v' <- vars t, v == v' ]

simpleRep :: PruningTerm -> State SimplePruner (Maybe PruningTerm)
simpleRep t = do
  S eqs <- get
  return (simplifies eqs t)

simplifies :: [(PruningTerm, PruningTerm)] -> PruningTerm -> Maybe PruningTerm
simplifies eqs t = msum [ simplifies1 (u, v) t `mplus` simplifies1 (v, u) t | (u, v) <- eqs ]

simplifies1 :: (PruningTerm, PruningTerm) -> PruningTerm -> Maybe PruningTerm
simplifies1 (t, u) v = do
  s <- match t v
  let w = subst s u
  guard (measure (fromPruningTerm w) < measure (fromPruningTerm v))
  return w
