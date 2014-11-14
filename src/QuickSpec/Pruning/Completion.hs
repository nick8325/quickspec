module QuickSpec.Pruning.Completion where

import QuickSpec.Base
import QuickSpec.Type
import QuickSpec.Utils
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
import Data.Maybe

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
    while KBC.complete (KBC.unpause >> generaliseRules)

while :: Monad m => m Bool -> m () -> m ()
while cond m = do
  x <- cond
  when x $ do
    m
    while cond m

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
      liftKBC $ while KBC.complete generaliseRules
      findRep axioms t

predecessors :: Monad m => PruningTerm -> StateT Completion m [PruningTerm]
--predecessors t = do
--  idx <- liftKBC $ gets (RuleIndex.invert . KBC.rules)
--  return (t:anywhere (tryRules idx) t)
predecessors t = return [t]

addAxiomsFor:: Monad m => PruningTerm -> StateT Completion m ()
addAxiomsFor t = do
  idx  <- liftKBC $ gets KBC.equations
  norm <- liftKBC KBC.normaliser
  let eqns =
        [ eqn
        | u <- subterms t,
          eqn <- map (bothSides norm . peel) (EquationIndex.lookup u idx),
          not (trivial eqn) ]
  mapM_ (liftKBC . KBC.traceM . KBC.NewGroundEquation) eqns
  liftKBC $ mapM_ KBC.newEquation eqns

generaliseRules :: Monad m => StateT KBC m ()
generaliseRules = do
  rules <- gets (map peel . RuleIndex.elems . KBC.rules)
  let p (Rule.Rule l r) = size l <= 5
      rules' = filter p (catMaybes (map (unskolemise . unorient >=> orient) rules))
  mapM_ (KBC.traceM . KBC.Generalise) rules'
  mapM_ (KBC.newEquation . unorient) rules'

unskolemise :: EquationOf PruningTerm -> Maybe (EquationOf PruningTerm)
unskolemise (l :==: r)
  | null [ () | SkolemVariable _ <- funs l ++ funs r ] = Nothing
  | otherwise = Just (rename f l' :==: rename f r')
  where
    l' :==: r' = canonicalise (unskolemiseTm (guardTerm l) :==: unskolemiseTm (guardTerm r))
    guardTerm t@(Fun (SkolemVariable x) []) = Fun (HasType (typ x)) [t]
    guardTerm t = t
    unskolemiseTm (Var x) = Var (Left x)
    unskolemiseTm (Fun (SkolemVariable x) []) = Var (Right x)
    unskolemiseTm (Fun f ts) = Fun f (map unskolemiseTm ts)
    f (Left x)  = x
    f (Right x) = PruningVariable (number x)

instance Pruner Completion where
  emptyPruner sig = initialState (maxTermSize_ sig)
  untypedRep Easy = findRep
  untypedRep Hard = findRepHarder
  untypedAxiom    = newAxiom
  pruningReport   = KBC.report . kbc
