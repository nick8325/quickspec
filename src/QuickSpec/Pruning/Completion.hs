module QuickSpec.Pruning.Completion where

import QuickSpec.Base
import QuickSpec.Pruning
import qualified QuickSpec.Pruning.KBC as KBC
import QuickSpec.Pruning.Equation
import QuickSpec.Pruning.Queue
import QuickSpec.Pruning.Rewrite
import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Signature
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Control.Monad
import qualified Data.Set as Set
import qualified QuickSpec.Pruning.RuleIndex as RuleIndex
import qualified QuickSpec.Pruning.EquationIndex as EquationIndex
import qualified Data.Rewriting.Rule as Rule
import Debug.Trace

newtype Completion =
  Completion {
    kbc       :: KBC }

type KBC = KBC.KBC PruningConstant PruningVariable

initialState :: Int -> Completion
initialState n =
  Completion {
    kbc       = KBC.initialState n }

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
  liftKBC $ do
    KBC.newEquation (t :==: u)
    res <- KBC.complete
    when res KBC.unpause

findRep :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT Completion m (Maybe PruningTerm)
findRep axioms t =
  localKBC $ do
    sequence_ [ KBC.newEquation (t :==: u) | [] :=>: t :=: u <- axioms ]
    KBC.complete
    norm <- KBC.normaliser
    let u = norm t
    if t == u then return Nothing else return (Just u)

findRepHarder :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT Completion m (Maybe PruningTerm)
findRepHarder axioms t = do
  u <- findRep axioms t
  case u of
    Just u -> return (Just u)
    Nothing -> do
      predecessors t >>= mapM_ addAxiomsFor
      findRep axioms t

predecessors :: Monad m => PruningTerm -> StateT Completion m [PruningTerm]
predecessors t = do
  idx <- liftKBC $ gets (RuleIndex.invert . KBC.rules)
  return (t:anywhere (tryRules idx) t)

addAxiomsFor:: Monad m => PruningTerm -> StateT Completion m ()
addAxiomsFor t = do
  idx <- liftKBC $ gets KBC.equations
  let eqns = concat [ EquationIndex.lookup u idx | u <- subterms t ]
  unless (null eqns) $
    traceM ("Adding ground equations " ++ prettyShow eqns)
  liftKBC $ mapM_ (KBC.newEquation . peel) eqns

instance Pruner Completion where
  emptyPruner sig = initialState (maxTermSize_ sig)
  untypedRep      = findRepHarder
  untypedAxiom    = newAxiom
  pruningReport   = KBC.report . kbc
