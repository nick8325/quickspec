-- Knuth-Bendix completion, up to an adjustable size limit.

{-# LANGUAGE CPP, TypeFamilies #-}
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
import QuickSpec.Pruning.Rule
import qualified Data.Rewriting.Rule as Rule
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Rewriting.CriticalPair as CP
import Data.Ord
import Data.Maybe
import QuickSpec.Pruning.Constraints
import Data.List

import qualified Debug.Trace

data Event f v = NewRule (Rule f v) | NewCPs [CP f v] | CaseSplit (Equation f v) (Constraint f v) (Set (Constraint f v)) | Pause (CEquation f v) | Reduce (Reduction f v) (Rule f v) | Complete | Unpausing
traceM :: (Monad m, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True ("New rule " ++ prettyShow rule)
traceM (NewCPs cps) = traceIf True ("New critical pairs " ++ prettyShow cps)
traceM (CaseSplit eqn cond conds) = traceIf True ("Case split on " ++ prettyShow cond ++ " for " ++ prettyShow eqn ++ " when " ++ prettyShow (Set.toList conds))
traceM (Pause (CEquation conds eqn)) = traceIf True ("Pausing equation " ++ prettyShow eqn ++ " under constraints " ++ prettyShow conds)
traceM (Reduce red rule) = traceIf True (prettyShow red ++ " using " ++ prettyShow rule)
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
    paused    :: Set (CEquation f v) }
  deriving Show

report :: KBC f v -> String
report s = show r ++ " rewrite rules, " ++ show c ++ " paused critical pairs.\n"
  where
    r = length (Index.elems (rules s))
    c = Set.size (paused s)

data CEquation f v =
  CEquation {
    constraints :: Constraints f v,
    equation    :: Equation f v }
  deriving (Eq, Ord, Show)

cequation :: (Sized f, Ord f, Ord v) => Constraints f v -> Equation f v -> CEquation f v
cequation conds eqn = CEquation conds (order eqn)

instance (Sized f, Ord f, Ord v, Numbered v) => Symbolic (CEquation f v) where
  type ConstantOf (CEquation f v) = f
  type VariableOf (CEquation f v) = v
  termsDL (CEquation conds eqn) = termsDL eqn `mplus` termsDL conds
  substf sub (CEquation conds eqn) =
    CEquation (substf sub conds) (substf sub eqn)

instance (PrettyTerm f, Pretty v) => Pretty (CEquation f v) where
  pretty (CEquation conds eqn) =
    hang (pretty conds <+> text "=>") 2 (pretty eqn)

data CP f v =
  CP {
    cpSize     :: Integer,
    cpEquation :: CEquation f v } deriving (Eq, Show)
instance (Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size (CEquation cs (l :==: r))) ->
      (Measure l, Measure r, size, constraintsSize cs, cs)
instance (PrettyTerm f, Pretty v) => Pretty (CP f v) where
  pretty = pretty . cpEquation

initialState :: Int -> KBC f v
initialState maxSize =
  KBC {
    maxSize   = maxSize,
    rules     = Index.empty,
    queue     = empty,
    paused    = Set.empty }

enqueueM ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (CP f v)] -> StateT (KBC f v) m ()
enqueueM l eqns = do
  unless (null eqns) $ traceM (NewCPs (map peel eqns))
  modify (\s -> s { queue = enqueue l eqns (queue s) })

dequeueM ::
  (Monad m, Sized f, Ord f, Ord v) =>
  StateT (KBC f v) m (Maybe (Label, Label, CP f v))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (l1, l2, x, q) -> (Just (l1, l2, x), s { queue = q })

newLabelM :: Monad m => StateT (KBC f v) m Label
newLabelM =
  state $ \s ->
    case newLabel (queue s) of
      (l, q) -> (l, s { queue = q })

pause :: (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Pretty v) => CEquation f v -> StateT (KBC f v) m ()
pause eqn = do
  traceM (Pause eqn)
  modify (\s -> s { paused = Set.insert eqn (paused s) })

normaliser ::
  (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) m (Constraints f v -> Tm f v -> Tm f v)
normaliser = do
  rules <- gets rules
  return $ \conds -> normaliseWith (anywhere (tryRules conds rules))

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
    Just (l1, l2, cp) -> do
      consider l1 l2 (cpEquation cp)
      complete1 True
    Nothing -> do
      when doneAnything $ traceM (Complete :: Event Constant Variable)
      return doneAnything

unpause ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) m ()
unpause = do
  paused  <- gets paused
  rules   <- gets rules
  let reduce conds = anywhere (tryRules conds rules)
      resumable (CEquation conds (t :==: u)) =
        reduce conds t /= [] || reduce conds u /= []
      (resumed, paused') = Set.partition resumable paused
  when (not (Set.null resumed)) $ do
    traceM (Unpausing :: Event Constant Variable)
    mapM_ newEquation (Set.toList resumed)
    modify (\s -> s { paused = paused' })
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
  CEquation f v -> StateT (KBC f v) m ()
newEquation eqn = queueCPs noLabel [unlabelled eqn]

queueCPs ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (CEquation f v)] -> StateT (KBC f v) m ()
queueCPs l eqns = do
  norm <- normaliser
  let cps = catMaybes (map (moveLabel . fmap (toCP norm)) eqns)
  enqueueM l cps

toCP ::
  (Sized f, Ord f, Ord v, Numbered v) =>
  (Constraints f v -> Tm f v -> Tm f v) ->
  CEquation f v -> Maybe (CP f v)
toCP norm (CEquation conds (l :==: r)) = do
  let l' = norm conds l
      r' = norm conds r
      eqn' = l' :==: r'
  guard (l' /= r')
  return (CP (minSize conds l' `max` minSize conds r') (CEquation conds (order eqn')))

consider ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> Label -> CEquation f v -> StateT (KBC f v) m ()
consider l1 l2 ceqn@(CEquation conds eqn) = do
  Debug.Trace.traceM ("Considering " ++ prettyShow ceqn)
  maxSize <- gets maxSize
  rules <- gets rules
  let eqns' = joinEquation rules (CEquation conds eqn)
  forM_ (Set.toList eqns') $ \(CEquation conds' eqn') ->
    if equationSize eqn' > fromIntegral maxSize
      then pause (CEquation conds' eqn')
      else
        forM_ (orient eqn') $ \rule -> do
          traceM (NewRule rule)
          l <- addRule rule
          interreduce rule
          addCriticalPairs l rule

joinEquation ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Labelled (Rule f v)) -> CEquation f v -> Set (CEquation f v)
joinEquation rules (CEquation conds eqn@(l :==: r))
  | l == r = Set.empty
  | l' == r' = Set.empty
  | otherwise =
    case findConstraint rules (CEquation conds eqn') of
      Nothing -> Set.singleton (canonicalise (CEquation conds eqn'))
      Just eqns ->
        Debug.Trace.trace ("Equation: " ++ prettyShow (CEquation conds eqn ) ++ "\nCase split:\n" ++ prettyShow eqns) $
        Set.unions [ joinEquation rules eqn' | eqn' <- eqns ]
    where
      norm = normaliseWith (anywhere (tryRules conds rules))
      l' = norm l
      r' = norm r
      eqn' = l' :==: r'

findConstraint ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Labelled (Rule f v)) -> CEquation f v -> Maybe [CEquation f v]
findConstraint rules (CEquation conds (t :==: u)) =
  fmap (usort . map canonicalise) (listToMaybe (catMaybes (map toObligs (sortBy (comparing goodness) (allRules t ++ allRules u)))))
  where
    allRules t = concat [map peel (Index.lookup u rules) | u <- usort (subterms t)]
    goodness rule = Measure (rhs rule)
    toObligs Rule { constraint = Just (l :<: r) } = do
      eqn1 <- tryCond (l :<: r)
      eqn2 <- tryCond (r :<: l)
      return ([eqn1, eqn2] ++ maybeToList (tryUnify l r))
    tryCond c = do
      conds' <- add c conds
      return (CEquation conds' (t :==: u))
    tryUnify l r = do
      sub <- unify l r
      conds' <- trySubst (evalSubst sub) conds
      return (CEquation conds' (substf (evalSubst sub) (t :==: u)))

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
  sequence_ [ newEquation (CEquation noConstraints (unorient rule)) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduce :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Rule f v -> Rule f v -> Maybe (Reduction f v)
reduce new@(Rule _ l r) old
  | not (l `isInstanceOf` lhs old) &&
    not (null (tryRule (ruleConstraints old) new (lhs old))) =
      Just (Reorient old)
  | not (null (tryRule (ruleConstraints old) new (rhs old))) =
      Just (Simplify old)
  | otherwise = Nothing

simplifyRule :: (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Label -> Rule f v -> StateT (KBC f v) m ()
simplifyRule l rl = do
  norm <- normaliser
  modify $ \s ->
    s{
      rules =
         Index.insert (Labelled l (fromMaybe __ (rule (lhs rl) (norm (ruleConstraints rl) (rhs rl)))))
           (Index.delete (Labelled l rl) (rules s)) }

addCriticalPairs :: (Monad m, PrettyTerm f, Ord f, Sized f, Ord v, Numbered v, Pretty v) => Label -> Rule f v -> StateT (KBC f v) m ()
addCriticalPairs l new = do
  rules <- gets rules
  queueCPs l $
    [ Labelled l' cp
    | Labelled l' old <- Index.elems rules,
      cp <- usort (criticalPairs new old ++ criticalPairs old new) ]

criticalPairs :: (Sized f, Ord f, Ord v, Numbered v) => Rule f v -> Rule f v -> [CEquation f v]
criticalPairs r1 r2 = do
  cp <- CP.cps [toRewritingRule r1] [toRewritingRule r2]
  let sub = CP.subst cp
      left = CP.left cp
      right = CP.right cp
      conds =
        map (substConstraint (evalSubst sub)) $
          [ substConstraint (Var . Left) cond | cond <- maybeToList (constraint r1) ] ++
          [ substConstraint (Var . Right) cond | cond <- maybeToList (constraint r2) ]

  let (left', (right', conds')) = canonicalise (left, (right, conds))
      f (Left x) = x
      f (Right x) = x
  conds'' <-
    maybeToList
      (foldM (flip add) noConstraints (map (substConstraint (Var . f)) conds'))
  return (CEquation conds'' (rename f left' :==: rename f right'))
