-- Knuth-Bendix completion, up to an adjustable size limit.
-- Doesn't deal with unorientable equations but keeps them around
-- for a higher level to use.

{-# LANGUAGE CPP #-}
module QuickSpec.Pruning.KBC where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Utils
import QuickSpec.Pruning
import QuickSpec.Pruning.Queue hiding (queue)
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import QuickSpec.Pruning.Equation
import QuickSpec.Pruning.Rewrite
import Data.Rewriting.Rule(Rule(..))
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Rewriting.CriticalPair as CP
import Data.Ord
import Data.Maybe
import Data.List

import qualified Debug.Trace

data Event f v =
    NewRule (Rule f v)
  | NewEquation (Equation f v)
  | Reduce (Reduction f v) (Rule f v)
  | Pause       (Equation f v)
  | Complete | Unpausing

traceM :: (Monad m, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True ("New rule " ++ prettyShow rule)
traceM (NewEquation eqn) = traceIf True ("New equation " ++ prettyShow eqn)
traceM (Reduce red rule) = traceIf True (prettyShow red ++ " using " ++ prettyShow rule)
traceM (Pause eqn) = traceIf True ("Pausing equation " ++ prettyShow eqn)
traceM Complete = traceIf True "Finished completion"
traceM Unpausing = traceIf True "Found rules to unpause"
traceIf :: Monad m => Bool -> String -> m ()
traceIf True s = Debug.Trace.traceM s
traceIf _ s = return ()

data KBC f v =
  KBC {
    maxSize   :: Int,
    rules     :: Index (Labelled (Rule f v)),
    queue     :: Queue (CP f v),
    equations :: Set (Equation f v),
    paused    :: Set (Equation f v) }
  deriving Show

newtype CP f v = CP (Equation f v) deriving (Eq, Show)
instance (Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare = comparing (\(CP (l :==: r)) -> (Measure l, Measure r, l, r))

report :: KBC f v -> String
report s = show r ++ " rewrite rules, " ++ show e ++ " equations, " ++ show c ++ " paused critical pairs.\n"
  where
    r = length (Index.elems (rules s))
    e = Set.size (equations s)
    c = Set.size (paused s)

initialState :: Int -> KBC f v
initialState maxSize =
  KBC {
    maxSize   = maxSize,
    rules     = Index.empty,
    queue     = empty,
    equations = Set.empty,
    paused    = Set.empty }

enqueueM ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (Equation f v)] -> StateT (KBC f v) m ()
enqueueM l eqns = do
  modify (\s -> s { queue = enqueue l (map (fmap (CP . order)) eqns) (queue s) })

dequeueM ::
  (Monad m, Sized f, Ord f, Ord v) =>
  StateT (KBC f v) m (Maybe (Label, Label, Equation f v))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (l1, l2, CP x, q) -> (Just (l1, l2, x), s { queue = q })

newLabelM :: Monad m => StateT (KBC f v) m Label
newLabelM =
  state $ \s ->
    case newLabel (queue s) of
      (l, q) -> (l, s { queue = q })

pause :: (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Pretty v, Numbered v) => Equation f v -> StateT (KBC f v) m ()
pause eqn = do
  traceM (Pause eqn)
  modify (\s -> s { paused = Set.insert (canonicalise eqn) (paused s) })

pauseEquation :: (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Pretty v, Numbered v) => Equation f v -> StateT (KBC f v) m ()
pauseEquation eqn = do
  traceM (NewEquation eqn)
  modify (\s -> s { equations = Set.insert (canonicalise eqn) (equations s) })

normaliser ::
  (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) m (Tm f v -> Tm f v)
normaliser = gets (normaliseWith . anywhere . tryRules . rules)

complete ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) m Bool
complete = complete1 False

complete1 ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Bool -> StateT (KBC f v) m Bool
complete1 doneAnything = do
  res <- dequeueM
  case res of
    Just (l1, l2, eqn) -> do
      consider l1 l2 eqn
      complete1 True
    Nothing -> do
      when doneAnything $ traceM (Complete :: Event Constant Variable)
      return doneAnything

unpause ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) m ()
unpause = do
  paused    <- gets paused
  equations <- gets equations
  rules   <- gets rules
  let reduce = anywhere (tryRules rules)
      resumable (t :==: u) = reduce t /= [] || reduce u /= []
      (resumed1, paused') = Set.partition resumable paused
      (resumed2, equations') = Set.partition resumable equations
      resumed = resumed1 `Set.union` resumed2
  when (not (Set.null resumed)) $ do
    traceM (Unpausing :: Event Constant Variable)
    mapM_ newEquation (Set.toList resumed)
    modify (\s -> s { paused = paused', equations = equations' })
    complete
    unpause

increaseSize ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Int -> StateT (KBC f v) m ()
increaseSize n = do
  m <- gets maxSize
  when (n > m) $ do
    modify (\s -> s { maxSize = n })
    unpause

newEquation ::
  (PrettyTerm f, Pretty v, Monad m, Sized f, Ord f, Ord v, Numbered v) =>
  Equation f v -> StateT (KBC f v) m ()
newEquation eqn = queueCPs noLabel [unlabelled eqn]

queueCPs ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (Equation f v)] -> StateT (KBC f v) m ()
queueCPs l eqns = do
  norm <- normaliser
  let cps = [ Labelled label (order (l' :==: r'))
            | Labelled label (l :==: r) <- eqns,
              let l' = norm l, let r' = norm r,
              l' /= r' ]
  enqueueM l cps

consider ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> Label -> Equation f v -> StateT (KBC f v) m ()
consider l1 l2 eqn = do
  maxSize <- gets maxSize
  norm    <- normaliser
  let eqn' = bothSides norm eqn
  unless (trivial eqn') $
    if equationSize eqn' > fromIntegral maxSize
      then pause eqn'
      else
        case orient eqn' of
          Just rule -> do
            traceM (NewRule rule)
            l <- addRule rule
            interreduce rule
            addCriticalPairs l rule
          Nothing ->
            pauseEquation eqn'

addRule :: (Monad m, PrettyTerm f, Ord f, Ord v, Numbered v, Pretty v) => Rule f v -> StateT (KBC f v) m Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { rules = Index.insert (Labelled l rule) (rules s) })
  return l

deleteRule :: (Monad m, Ord f, Ord v, Numbered v) => Label -> Rule f v -> StateT (KBC f v) m ()
deleteRule l rule =
  modify $ \s ->
    s { rules = Index.delete (Labelled l rule) (rules s),
        queue = deleteLabel l (queue s) }

data Reduction f v = Simplify (Rule f v) | Reorient (Rule f v) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Reduction f v) where
  pretty (Simplify rule) = text "Simplify" <+> pretty rule
  pretty (Reorient rule) = text "Reorient" <+> pretty rule

interreduce :: (Monad m, PrettyTerm f, Ord f, Sized f, Ord v, Numbered v, Pretty v) => Rule f v -> StateT (KBC f v) m ()
interreduce new = do
  rules <- gets (Index.elems . rules)
  let reductions = catMaybes (map (moveLabel . fmap (reduce new)) rules)
  sequence_ [ traceM (Reduce red new) | red <- map peel reductions ]
  sequence_ [ simplifyRule l rule | Labelled l (Simplify rule) <- reductions ]
  sequence_ [ newEquation (unorient rule) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduce :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Rule f v -> Rule f v -> Maybe (Reduction f v)
reduce new@(Rule l r) old
  | not (l `isInstanceOf` lhs old) &&
    not (null (tryRule new (lhs old))) =
      Just (Reorient old)
  | not (null (tryRule new (rhs old))) =
      Just (Simplify old)
  | otherwise = Nothing

simplifyRule :: (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Label -> Rule f v -> StateT (KBC f v) m ()
simplifyRule l rule = do
  norm <- normaliser
  modify $ \s ->
    s{
      rules =
         Index.insert (Labelled l rule { rhs = norm (rhs rule) })
           (Index.delete (Labelled l rule) (rules s)) }

addCriticalPairs :: (Monad m, PrettyTerm f, Ord f, Sized f, Ord v, Numbered v, Pretty v) => Label -> Rule f v -> StateT (KBC f v) m ()
addCriticalPairs l new = do
  rules <- gets rules
  queueCPs l $
    [ Labelled l' cp
    | Labelled l' old <- Index.elems rules,
      cp <- usort (criticalPairs new old ++ criticalPairs old new) ]

criticalPairs :: (Ord f, Ord v, Numbered v) => Rule f v -> Rule f v -> [Equation f v]
criticalPairs r1 r2 = do
  cp <- CP.cps [r1] [r2]
  let sub = CP.subst cp
      left = CP.left cp
      right = CP.right cp

  let (left', right') = canonicalise (left, right)
      f (Left x) = x
      f (Right x) = x
  return (rename f left' :==: rename f right')
