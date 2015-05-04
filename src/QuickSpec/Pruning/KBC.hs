-- Knuth-Bendix completion, up to an adjustable size limit.
-- Does constrained rewriting for unorientable equations.

{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts #-}
module QuickSpec.Pruning.KBC where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Pruning.Constraints
import QuickSpec.Pruning.Equation
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import QuickSpec.Pruning.Queue hiding (queue)
import QuickSpec.Pruning.Rewrite
import QuickSpec.Term
import QuickSpec.Utils
import Control.Monad
import Data.List
import Data.Maybe
import Data.Ord
import Data.Functor.Identity
import qualified Data.Rewriting.CriticalPair as CP
import Data.Rewriting.Rule(Rule(..))
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Debug.Trace
import QuickSpec.Pruning.FourierMotzkin((<==))
import Control.Monad.Trans.State.Strict

data Event f v =
    NewRule (Constrained (Rule f v))
  | NewAxiom (Equation f v)
  | ExtraRule (Constrained (Rule f v))
  | NewCP (CP f v)
  | Consider (Constrained (Rule f v)) (Context f v)
  | Reduce (Reduction f v) (Constrained (Rule f v))

traceM :: (Monad m, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True (hang (text "New rule") 2 (pretty rule))
traceM (NewAxiom axiom) = traceIf True (hang (text "New axiom") 2 (pretty axiom))
traceM (ExtraRule rule) = traceIf True (hang (text "Extra rule") 2 (pretty rule))
traceM (NewCP cps) = traceIf False (hang (text "Critical pair") 2 (pretty cps))
traceM (Consider eq ctx) = traceIf False (sep [text "Considering", nest 2 (pretty eq), text "under", nest 2 (pretty ctx)])
traceM (Reduce red rule) = traceIf True (sep [pretty red, nest 2 (text "using"), nest 2 (pretty rule)])
traceIf :: Monad m => Bool -> Doc -> m ()
--traceIf True x = Debug.Trace.traceM (show x)
traceIf _ s = return ()

data KBC f v =
  KBC {
    maxSize       :: Int,
    labelledRules :: Index (Labelled (Constrained (Rule f v))),
    extraRules    :: Index (Constrained (Rule f v)),
    queue         :: Queue (CP f v) }
  deriving Show

data CP f v =
  CP {
    cpSize     :: Integer,
    cpEquation :: Constrained (Equation f v) } deriving (Eq, Show)

instance (Minimal f, Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size (Constrained ctx (l :==: r))) ->
      (measure l, measure r, size)

instance (PrettyTerm f, Pretty v) => Pretty (CP f v) where
  pretty = pretty . cpEquation

report :: KBC f v -> String
report s = show r ++ " rewrite rules, " ++ show e ++ " extra rewrite rules."
  where
    r = length (Index.elems (labelledRules s))
    e = length (Index.elems (extraRules s))

initialState :: Int -> KBC f v
initialState maxSize =
  KBC {
    maxSize       = maxSize,
    labelledRules = Index.empty,
    extraRules    = Index.empty,
    queue         = empty }

enqueueM ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (CP f v)] -> StateT (KBC f v) IO ()
enqueueM l eqns = do
  modify (\s -> s { queue = enqueue l eqns (queue s) })

dequeueM ::
  (Minimal f, Sized f, Ord f, Ord v) =>
  StateT (KBC f v) IO (Maybe (Label, Label, CP f v))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (l1, l2, x, q) -> (Just (l1, l2, x), s { queue = q })

newLabelM :: StateT (KBC f v) IO Label
newLabelM =
  state $ \s ->
    case newLabel (queue s) of
      (l, q) -> (l, s { queue = q })

rules :: KBC f v -> Index (Constrained (Rule f v))
rules = Index.mapMonotonic peel id id . labelledRules

allRules :: (Minimal f, Sized f, Numbered v, Ord f, Ord v) => KBC f v -> Index (Constrained (Rule f v))
allRules x = rules x `Index.union` extraRules x

constrainedNormaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) IO (Context f v -> Tm f v -> Tm f v)
constrainedNormaliser = do
  rules <- gets allRules
  return $ \ctx -> normaliseWith (anywhere (tryConstrainedRules ctx rules))

specificNormaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) IO (Set (Formula f v) -> Tm f v -> Tm f v)
specificNormaliser = do
  rules <- gets allRules
  return $ \forms ->
    normaliseWith (anywhere (trySpecificRules forms rules))

normaliser ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) IO (Tm f v -> Tm f v)
normaliser = do
  rules <- gets allRules
  return $
    normaliseWith (anywhere (tryRules rules))

complete ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) IO ()
complete = do
  res <- dequeueM
  case res of
    Just (l1, l2, cp) -> do
      consider l1 l2 (cpEquation cp)
      complete
    Nothing ->
      return ()

newEquation ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) =>
  Constrained (Equation f v) -> StateT (KBC f v) IO ()
newEquation (Constrained ctx (t :==: u)) = do
  n <- gets maxSize
  queueCPs noLabel (map unlabelled (split (Constrained (toContext FTrue) (t :==: u))))

queueCPs ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (Constrained (Equation f v))] -> StateT (KBC f v) IO ()
queueCPs l eqns = do
  norm <- normaliser
  n <- gets maxSize
  let cps = catMaybes (map (moveLabel . fmap (toCP norm)) eqns)
      cps' = [ cp | cp <- cps, cpSize (peel cp) <= fromIntegral n ]
  mapM_ (traceM . NewCP . peel) cps'
  enqueueM l cps'

toCP ::
  (Minimal f, Sized f, Ord f, Ord v, Numbered v, PrettyTerm f, Pretty v) =>
  (Tm f v -> Tm f v) ->
  Constrained (Equation f v) -> Maybe (CP f v)
toCP norm (Constrained ctx (l :==: r)) = do
  guard (l /= r)
  let l' :==: r' = order (norm l :==: norm r)
      ctx' = minimiseContext l' ctx
  guard (l' /= r')
  return (CP (modelSize l' (solved ctx')) (canonicalise (Constrained ctx' (l' :==: r'))))

-- Plan:
-- 1. Normalise without case split.
-- 2. Orient remaining critical pair. Each resulting split might give us a condition.
-- 3. Normalise each critical pair without case split.
-- 4. Normalise each critical pair with case split.
-- If we normalise after step 4, add the critical pair to the extra rules.

normalisePair ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Context f v -> Equation f v -> StateT (KBC f v) IO (Equation f v)
normalisePair ctx (t :==: u) = do
  norm <- normaliser
  snorm <- specificNormaliser
  rules <- gets allRules
  let aux forms t u
        | t == u = t :==: u
        | forms == forms' = t' :==: u'
        | otherwise = aux forms' t' u'
        where
          forms' = Set.union forms (Set.fromList (impliedCases rules ctx (t' :==: u')))
          t' = snorm forms t
          u' = snorm forms u
  return $! aux Set.empty (norm t) (norm u)

impliedCases ::
  (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Constrained (Rule f v)) ->
  Context f v -> Equation f v -> [Formula f v]
impliedCases rules ctx (t :==: u) = do
  v <- usort (subterms t ++ subterms u)
  rule <- Index.lookup v rules
  let form = formula (context rule)
  guard (any (implies (solved ctx)) (mainSplits form))
  return form

consider ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> Label -> Constrained (Equation f v) -> StateT (KBC f v) IO ()
consider l1 l2 (Constrained ctx (t :==: u)) = do
  t :==: u <- normalisePair ctx (t :==: u)
  forM_ (orient (t :==: u)) $
    \(Constrained ctx' (Rule t u)) ->
    forM_ (usort (map canonicalise (split (Constrained ctx' (Rule t u, ctx))))) $
      \(Constrained ctx' (Rule t u, ctx)) -> do
        let rule = Constrained ctx' (Rule t u)
        traceM (Consider rule ctx)
        let rules = split (Constrained (toContext (formula ctx &&& formula ctx')) (t :==: u))
        res <- andM (map joinable rules)
        unless res $ do
          traceM (NewRule rule)
          l <- addRule rule
          interreduce rule
          addCriticalPairs l rule

andM :: [StateT (KBC f v) IO Bool] -> StateT (KBC f v) IO Bool
andM [] = return True
andM (mx:xs) = do
  x <- mx
  if x then andM xs else return False

joinable ::
  (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Constrained (Equation f v) -> StateT (KBC f v) IO Bool
joinable (Constrained ctx eq) =
  andM $ do
    Constrained ctx' (Rule t u) <- orient eq
    Constrained ctx (Rule t u) <- split (Constrained (toContext (formula ctx &&& formula ctx')) (Rule t u))
    return $ do
      t' :==: u' <- normalisePair ctx (t :==: u)
      case () of
        () | t' == u' -> return True
           | t == t' && u == u' -> return False
           | otherwise -> joinable (Constrained ctx (t' :==: u'))

addRule :: (PrettyTerm f, Minimal f, Sized f, Ord f, Ord v, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) IO Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  return l

deleteRule :: (Minimal f, Sized f, Ord f, Ord v, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) IO ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Reduction f v = Simplify (Constrained (Rule f v)) | Reorient (Constrained (Rule f v)) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Reduction f v) where
  pretty (Simplify rule) = text "Simplify" <+> pretty rule
  pretty (Reorient rule) = text "Reorient" <+> pretty rule

interreduce :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) IO ()
interreduce new = do
  rules <- gets (Index.elems . labelledRules)
  let reductions = catMaybes (map (moveLabel . fmap (reduceWith new)) rules)
  sequence_ [ traceM (Reduce red new) | red <- map peel reductions ]
  sequence_ [ simplifyRule l rule | Labelled l (Simplify rule) <- reductions ]
  sequence_ [ newEquation (Constrained (toContext FTrue) (unorient (constrained rule))) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduceWith :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) => Constrained (Rule f v) -> Constrained (Rule f v) -> Maybe (Reduction f v)
reduceWith new old
  | not (lhs (constrained new) `isInstanceOf` lhs (constrained old)) &&
    not (null (tryRule (context old) new (lhs (constrained old)))) =
      Just (Reorient old)
  | not (null (tryRule (context old) new (rhs (constrained old)))) =
      Just (Simplify old)
  | otherwise = Nothing

simplifyRule :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) IO ()
simplifyRule l rule@(Constrained ctx (Rule lhs rhs)) = do
  norm <- constrainedNormaliser
  modify $ \s ->
    s {
      labelledRules =
         Index.insert (Labelled l (Constrained ctx (Rule lhs (norm ctx rhs))))
           (Index.delete (Labelled l rule) (labelledRules s)) }

addCriticalPairs :: (PrettyTerm f, Ord f, Minimal f, Sized f, Ord v, Numbered v, Pretty v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) IO ()
addCriticalPairs l new = do
  rules <- gets labelledRules
  size  <- gets maxSize
  queueCPs l $
    [ Labelled l' cp
    | Labelled l' old <- Index.elems rules,
      cp <- usort (criticalPairs size new old ++ criticalPairs size old new) ]

canonicaliseBoth :: (Symbolic a, Ord (VariableOf a), Numbered (VariableOf a)) => (a, a) -> (a, a)
canonicaliseBoth (x, y) = (x', substf (Var . increase) y')
  where
    x' = canonicalise x
    y' = canonicalise y
    n  = maximum (0:map (succ . number) (vars x'))
    increase v = withNumber (n+number v) v

criticalPairs :: (PrettyTerm f, Pretty v, Minimal f, Sized f, Ord f, Ord v, Numbered v) => Int -> Constrained (Rule f v) -> Constrained (Rule f v) -> [Constrained (Equation f v)]
criticalPairs n r1 r2 = do
  guard (not (or [ funSize f == 0 && funArity f == 1 | f <- funs (lhs (constrained r1)) ++ funs (lhs (constrained r2)) ]))
  let (Constrained ctx1 r1', Constrained ctx2 r2') = canonicaliseBoth (r1, r2)
  cp <- CP.cps [r1'] [r2']
  let sub = CP.subst cp
      f (Left x)  = x
      f (Right x) = x
      left = rename f (CP.left cp)
      right = rename f (CP.right cp)
      ctx =
        toContext $
          substf (rename f . evalSubst sub . Left) (formula ctx1) &&&
          substf (rename f . evalSubst sub . Right) (formula ctx2)

  split (Constrained ctx (left :==: right))
