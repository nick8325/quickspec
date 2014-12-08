-- Knuth-Bendix completion, up to an adjustable size limit.
-- Doesn't deal with unorientable equations but keeps them around
-- for a higher level to use.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts #-}
module QuickSpec.Pruning.KBC where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Utils
import QuickSpec.Pruning
import QuickSpec.Pruning.Queue hiding (queue)
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import QuickSpec.Pruning.Constraints
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
    NewRule (Constrained (Rule f v))
  | NewCPs [CP f v]
  | Consider (Constrained (Equation f v))
  | CaseSplit (Constrained (Equation f v)) (Context f v) [Constrained (Equation f v)]
  | ConsiderCaseSplit (Constrained (Equation f v)) (Context f v)
  | Pause (Constrained (Equation f v))
  | Reduce (Reduction f v) (Constrained (Rule f v))
  | Complete
  | Unpausing

traceM :: (Monad m, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True (hang (text "New rule") 2 (pretty rule))
traceM (NewCPs cps) = traceIf False (hang (text "New critical pairs") 2 (pretty cps))
traceM (Consider eq) = traceIf False (hang (text "Considering") 2 (pretty eq))
traceM (CaseSplit eqn ctx eqns) = traceIf False (sep [text "Case split on", nest 2 (pretty ctx), text "in", nest 2 (pretty eqn), text "giving", nest 2 (pretty eqns)])
traceM (ConsiderCaseSplit ctx ctx') = traceIf False (sep [text "Considering case split on", nest 2 (pretty ctx'), text "in", nest 2 (pretty ctx)])
traceM (Pause eqn) = traceIf False (hang (text "Pausing equation") 2 (pretty eqn))
traceM (Reduce red rule) = traceIf True (sep [pretty red, nest 2 (text "using"), nest 2 (pretty rule)])
traceM Complete = traceIf True (text "Finished completion")
traceM Unpausing = traceIf True (text "Found rules to unpause")
traceIf :: Monad m => Bool -> Doc -> m ()
traceIf True x = Debug.Trace.traceM (show x)
traceIf _ s = return ()

data KBC f v =
  KBC {
    maxSize   :: Int,
    rules     :: Index (Labelled (Constrained (Rule f v))),
    queue     :: Queue (CP f v),
    paused    :: Set (Constrained (Equation f v)) }
  deriving Show

data CP f v =
  CP {
    cpSize     :: Integer,
    cpEquation :: Constrained (Equation f v) } deriving (Eq, Show)

instance (Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size (Constrained ctx (l :==: r))) ->
      (measure l, measure r, size, Set.size (literals ctx), literals ctx)

instance (PrettyTerm f, Pretty v) => Pretty (CP f v) where
  pretty = pretty . cpEquation

report :: KBC f v -> String
report s = show r ++ " rewrite rules, " ++ show c ++ " paused critical pairs.\n"
  where
    r = length (Index.elems (rules s))
    c = Set.size (paused s)

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

pause :: (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Pretty v, Numbered v) => Constrained (Equation f v) -> StateT (KBC f v) m ()
pause eqn = do
  traceM (Pause eqn)
  modify (\s -> s { paused = Set.insert (canonicalise eqn) (paused s) })

normaliser ::
  (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) m (Context f v -> Tm f v -> Tm f v)
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
      mapM_ (consider l1 l2) (split (cpEquation cp))
      complete1 True
    Nothing -> do
      when doneAnything $ traceM (Complete :: Event Constant Variable)
      return doneAnything

unpause ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) m ()
unpause = do
  paused    <- gets paused
  rules   <- gets rules
  let resumable eq = not (null (concatMap (caseSplit rules) (split eq)))
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
  Constrained (Equation f v) -> StateT (KBC f v) m ()
newEquation eqn = queueCPs noLabel (map unlabelled (split eqn))

queueCPs ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (Constrained (Equation f v))] -> StateT (KBC f v) m ()
queueCPs l eqns = do
  norm <- normaliser
  n    <- gets maxSize
  let cps = catMaybes (map (moveLabel . fmap (toCP norm)) eqns)
      p (Labelled _ (CP m _)) = m <= fromIntegral n
      (cps1, cps2) = partition p cps
  enqueueM l cps1
  sequence_ [ pause eq | Labelled _ (CP _ eq) <- cps2 ]

toCP ::
  (Sized f, Ord f, Ord v, Numbered v, PrettyTerm f, Pretty v) =>
  (Context f v -> Tm f v -> Tm f v) ->
  Constrained (Equation f v) -> Maybe (CP f v)
toCP norm (Constrained ctx (l :==: r)) = do
  let l' = norm ctx l
      r' = norm ctx r
      eqn' = order (l' :==: r')
  guard (l' /= r')
  return (CP (minSize l' ctx `max` minSize r' ctx) (canonicalise (Constrained ctx eqn')))

consider ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> Label -> Constrained (Equation f v) -> StateT (KBC f v) m ()
consider l1 l2 eq = do
  traceM (Consider eq)
  rules <- gets rules
  case joinEquation rules eq of
    GaveUp (Constrained ctx eq) ->
      forM_ (orient eq >>= split . canonicalise) $ \rule -> do
        traceM (NewRule rule)
        l <- addRule rule
        interreduce rule
        addCriticalPairs l rule
    ReducedTo ctx eqs -> do
      unless (null eqs) $
        traceM (CaseSplit eq ctx eqs)
      queueCPs l1 (map (Labelled l2) eqs)

data JoinResult f v = GaveUp (Constrained (Equation f v)) | ReducedTo (Context f v) [Constrained (Equation f v)]

joinEquation ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Labelled (Constrained (Rule f v))) -> Constrained (Equation f v) -> JoinResult f v
joinEquation rules (Constrained ctx eq@(l :==: r))
  | l == r = ReducedTo emptyContext []
  | l' == r' = ReducedTo emptyContext []
  | otherwise =
    case bestCaseSplit rules (Constrained ctx eq') of
      Nothing -> GaveUp (Constrained ctx eq')
      Just (ctx, eqs) -> ReducedTo ctx eqs
    where
      norm = normaliseWith (anywhere (tryRules ctx rules))
      l' = norm l
      r' = norm r
      eq' = l' :==: r'

bestCaseSplit ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Labelled (Constrained (Rule f v))) -> Constrained (Equation f v) -> Maybe (Context f v, [Constrained (Equation f v)])
bestCaseSplit rules eq =
  listToMaybe (sortBy' goodness (filter p (caseSplit rules eq)))
  where
    goodness (_, eqs@(Constrained ctx (l :==: r):_)) =
      (length eqs, l' `max` r', l', r')
      where
        norm = normaliseWith (anywhere (tryRules ctx rules))
        l' = measure (norm l)
        r' = measure (norm r)
    p (_, eqs) = eq `notElem` eqs

caseSplit ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Labelled (Constrained (Rule f v))) -> Constrained (Equation f v) -> [(Context f v, [Constrained (Equation f v)])]
caseSplit rules (Constrained ctx eq@(l :==: r)) = usort $ do
  t <- subterms l ++ subterms r
  Constrained ctx' _ <- map peel (Index.lookup t rules)
  traceM (ConsiderCaseSplit (Constrained ctx eq) ctx')
  let pos = split (Constrained (contextUnion ctx ctx') eq)
      neg = addNegation ctx' (Constrained ctx eq)
  guard (pos /= [])
  return (ctx', usort (map canonicalise (pos ++ neg)) >>= split)

addRule :: (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) m Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { rules = Index.insert (Labelled l rule) (rules s) })
  return l

deleteRule :: (Monad m, Sized f, Ord f, Ord v, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) m ()
deleteRule l rule =
  modify $ \s ->
    s { rules = Index.delete (Labelled l rule) (rules s),
        queue = deleteLabel l (queue s) }

data Reduction f v = Simplify (Constrained (Rule f v)) | Reorient (Constrained (Rule f v)) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Reduction f v) where
  pretty (Simplify rule) = text "Simplify" <+> pretty rule
  pretty (Reorient rule) = text "Reorient" <+> pretty rule

interreduce :: (Monad m, PrettyTerm f, Ord f, Sized f, Ord v, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) m ()
interreduce new = do
  rules <- gets (Index.elems . rules)
  let reductions = catMaybes (map (moveLabel . fmap (reduce new)) rules)
  sequence_ [ traceM (Reduce red new) | red <- map peel reductions ]
  sequence_ [ simplifyRule l rule | Labelled l (Simplify rule) <- reductions ]
  sequence_ [ newEquation (unconstrained (unorient (constrained rule))) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduce :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Constrained (Rule f v) -> Constrained (Rule f v) -> Maybe (Reduction f v)
reduce new old
  | not (lhs (constrained new) `isInstanceOf` lhs (constrained old')) &&
    not (null (tryRule (context old') new (lhs (constrained old')))) =
      Just (Reorient old')
  | not (null (tryRule (context old') new (rhs (constrained old')))) =
      Just (Simplify old')
  | otherwise = Nothing
  where
    [old'] = split old

simplifyRule :: (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) m ()
simplifyRule l rule@(Constrained ctx (Rule lhs rhs)) = do
  norm <- normaliser
  modify $ \s ->
    s {
      rules =
         Index.insert (Labelled l (Constrained ctx (Rule lhs (norm ctx rhs))))
           (Index.delete (Labelled l rule) (rules s)) }

addCriticalPairs :: (Monad m, PrettyTerm f, Ord f, Sized f, Ord v, Numbered v, Pretty v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) m ()
addCriticalPairs l new = do
  rules <- gets rules
  queueCPs l $
    [ Labelled l' cp
    | Labelled l' old <- Index.elems rules,
      cp <- usort (criticalPairs new old ++ criticalPairs old new) ]

canonicaliseBoth :: (Symbolic a, Ord (VariableOf a), Numbered (VariableOf a)) => (a, a) -> (a, a)
canonicaliseBoth (x, y) = (x', substf (Var . increase) y')
  where
    x' = canonicalise x
    y' = canonicalise y
    n  = maximum (0:map (succ . number) (vars x'))
    increase v = withNumber (n+number v) v

criticalPairs :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Constrained (Rule f v) -> Constrained (Rule f v) -> [Constrained (Equation f v)]
criticalPairs r1 r2 = do
  let (Constrained ctx1 r1', Constrained ctx2 r2') = canonicaliseBoth (r1, r2)
  cp <- CP.cps [r1'] [r2']
  let sub = CP.subst cp
      f (Left x)  = x
      f (Right x) = x
      left = rename f (CP.left cp)
      right = rename f (CP.right cp)
      ctx =
        contextUnion
          (substf (rename f . evalSubst sub . Left) ctx1)
          (substf (rename f . evalSubst sub . Right) ctx2)

  split (Constrained ctx (left :==: right))
