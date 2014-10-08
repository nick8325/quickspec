module Test.QuickSpec.Pruning.Simple where

import Test.QuickSpec.Base
import Test.QuickSpec.Term
import Test.QuickSpec.Pruning
import Control.Monad
import Control.Monad.Trans.State.Strict

newtype SimplePruner = S [(PruningTerm, PruningTerm)]

instance Pruner SimplePruner where
  emptyPruner = S []
  unifyUntyped = simpleUnify
  repUntyped = simpleRep

simpleUnify :: PruningTerm -> PruningTerm -> State SimplePruner Bool
simpleUnify t u
  | measure (decodeTypes t) < measure (decodeTypes u) = simpleUnify u t
simpleUnify u t = do
  S eqs <- get
  case simplifies eqs u of
    Just v -> do
      unless (decodeTypes v `alwaysSimplerThan` decodeTypes t ||
              decodeTypes v `alwaysSimplerThan` decodeTypes u)
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
  guard (measure (decodeTypes w) < measure (decodeTypes v))
  return w
