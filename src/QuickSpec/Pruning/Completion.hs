module QuickSpec.Pruning.Completion where

import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Pruning.Constraints
import QuickSpec.Pruning.Equation
import qualified QuickSpec.Pruning.KBC as KBC
import QuickSpec.Signature
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import qualified QuickSpec.Pruning.Index as Index

newtype Completion =
  Completion {
    kbc       :: KBC }

type KBC = KBC.KBC PruningConstant PruningVariable

initialState :: Int -> Completion
initialState n =
  Completion {
    kbc       = KBC.initialState n }

liftKBC :: StateT KBC IO a -> StateT Completion IO a
liftKBC m = do
  s <- get
  (x, ks) <- lift (runStateT m (kbc s))
  put s { kbc = ks }
  return x

localKBC :: StateT KBC IO a -> StateT Completion IO a
localKBC m = do
  ks <- gets kbc
  lift (evalStateT m ks)

newAxiom :: AxiomMode -> PropOf PruningTerm -> StateT Completion IO ()
newAxiom Normal ([] :=>: (t :=: u)) = do
  liftKBC $ do
    KBC.traceM (KBC.NewAxiom (t :==: u))
    norm <- KBC.normaliser
    unless (norm t == norm u) $ do
      KBC.newEquation (Constrained (toContext FTrue) (t :==: u))
      KBC.complete
newAxiom WithoutConsequences ([] :=>: (t :=: u)) = do
  liftKBC $ do
    KBC.traceM (KBC.NewAxiom (t :==: u))
    norm <- KBC.normaliser
    forM_ (orient (norm t :==: norm u) >>= split) $ \rule ->
      modify (\s -> s { KBC.extraRules = Index.insert rule (KBC.extraRules s) })
newAxiom _ _ = return ()

while :: IO Bool -> IO () -> IO ()
while cond m = do
  x <- cond
  when x $ do
    m
    while cond m

findRep :: [PropOf PruningTerm] -> PruningTerm -> StateT Completion IO (Maybe PruningTerm)
findRep axioms t =
  localKBC $ do
    sequence_ [ KBC.newEquation (Constrained (toContext FTrue) (t :==: u)) | [] :=>: t :=: u <- axioms ]
    KBC.complete
    norm <- KBC.normaliser
    let u = norm t
    if t == u then return Nothing else return (Just u)

instance Pruner Completion where
  emptyPruner sig = initialState (maxTermSize_ sig)
  untypedRep      = findRep
  untypedAxiom    = newAxiom
  pruningReport   = KBC.report . kbc
