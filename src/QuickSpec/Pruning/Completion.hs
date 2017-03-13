module QuickSpec.Pruning.Completion where

import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Signature
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Twee.Base
import qualified Twee.Rule as Rule
import qualified Twee as Twee
import Twee(Twee)
import Debug.Trace

newtype Completion =
  Completion {
    twee       :: Twee PruningConstant }

initialState :: Int -> Completion
initialState n =
  Completion {
    twee       = (Twee.initialState 0 1) { Twee.maxSize = Just n, Twee.tracing = False, Twee.maxCancellationSize = Just 0 } }

liftTwee :: State (Twee PruningConstant) a -> StateT Completion IO a
liftTwee m = do
  s <- get
  let (x, ks) = runState m (twee s)
  put $! s { twee = ks }
  return $! x

localTwee :: State (Twee PruningConstant) a -> StateT Completion IO a
localTwee m = do
  ks <- gets twee
  return $! evalState m ks

newAxiom :: AxiomMode -> PropOf PruningTerm -> StateT Completion IO ()
newAxiom _ ([] :=>: (t :=: u)) = do
  liftTwee $ do
    s <- get
    let norm = Rule.result . Twee.normalise s
    unless (norm t == norm u) $ do
      Twee.newEquation (t Rule.:=: u)
      Twee.complete
  return ()
newAxiom _ _ = return ()

while :: IO Bool -> IO () -> IO ()
while cond m = do
  x <- cond
  when x $ do
    m
    while cond m

findRep :: [PropOf PruningTerm] -> PruningTerm -> StateT Completion IO (Maybe PruningTerm)
findRep axioms t =
  localTwee $ do
    sequence_ [ Twee.newEquation (t Rule.:=: u) | [] :=>: t :=: u <- axioms ]
    s <- get
    let u = Rule.result (Twee.normalise s t)
    if t == u then return Nothing else return (Just u)

instance Pruner Completion where
  emptyPruner sig = initialState (maxPruningSize_ sig)
  untypedRep      = findRep
  untypedAxiom    = newAxiom
  pruningReport   = Twee.report . twee
