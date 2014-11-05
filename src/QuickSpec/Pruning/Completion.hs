module QuickSpec.Pruning.Completion where

import QuickSpec.Pruning
import qualified QuickSpec.Pruning.KBC as KBC
import QuickSpec.Pruning.Equation
import QuickSpec.Prop
import QuickSpec.Term
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class

data Completion =
  Completion {
    sizeDelta :: Int,
    kbc       :: KBC }

type KBC = KBC.KBC PruningConstant PruningVariable

initialState :: Completion
initialState =
  Completion {
    sizeDelta = 5,
    kbc       = KBC.initialState 0 }

seenTerm :: Monad m => PruningTerm -> StateT Completion m ()
seenTerm t = do
  n <- gets sizeDelta
  liftKBC $ KBC.increaseSize (size t+n)

liftKBC :: Monad m => StateT KBC m a -> StateT Completion m a
liftKBC m = do
  s <- get
  (x, ks) <- lift (runStateT m (kbc s))
  put s { kbc = ks }
  return x

localKBC :: Monad m => StateT KBC m a -> StateT Completion m a
localKBC m = do
  ks <- gets kbc
  lift (evalStateT m ks)

newAxiom :: Monad m => PropOf PruningTerm -> StateT Completion m ()
newAxiom ([] :=>: (t :=: u)) = do
  seenTerm t
  seenTerm u
  liftKBC $ do
    KBC.newEquation (t :==: u)
    KBC.complete
    KBC.unpause

findRep :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT Completion m (Maybe PruningTerm)
findRep axioms t = do
  seenTerm t
  sequence_ [ do { seenTerm t; seenTerm u } | [] :=>: (t :=: u) <- axioms ]
  localKBC $ do
    sequence_ [ KBC.newEquation (t :==: u) | [] :=>: (t :=: u) <- axioms ]
    KBC.complete
    norm <- KBC.normaliser
    let u = norm t
    if t == u then return Nothing else return (Just u)

instance Pruner Completion where
  emptyPruner = initialState
  untypedRep = findRep
  untypedAxiom = newAxiom
