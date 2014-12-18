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
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Class
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.Rewriting.CriticalPair as CP
import Data.Rewriting.Rule(Rule(..))
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Debug.Trace
import QuickSpec.Pruning.FourierMotzkin((<==))

data Event f v =
    NewRule (Constrained (Rule f v))
  | NewCPs [CP f v]
  | Consider (Constrained (Equation f v))
  | CaseSplit (Context f v) (Formula f v) (Rule f v)
  | ConditionalJoin (Constrained (Equation f v)) (Formula f v)
  | Reduce (Reduction f v) (Constrained (Rule f v))

traceM :: (Monad m, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True (hang (text "New rule") 2 (pretty rule))
traceM (NewCPs cps) = traceIf False (hang (text "New critical pairs") 2 (pretty cps))
traceM (Consider eq) = traceIf True (hang (text "Considering") 2 (pretty eq))
traceM (CaseSplit ctx form rule) = traceIf False (sep [text "Splitting on", nest 2 (pretty form), text "in", nest 2 (pretty ctx), text "to apply", nest 2 (pretty rule)])
traceM (ConditionalJoin eq form) = traceIf False (sep [text "Conditionally joined", nest 2 (pretty eq), text "assuming", nest 2 (pretty form)])
traceM (Reduce red rule) = traceIf True (sep [pretty red, nest 2 (text "using"), nest 2 (pretty rule)])
traceIf :: Monad m => Bool -> Doc -> m ()
traceIf True x = Debug.Trace.traceM (show x)
traceIf _ s = return ()

data KBC f v =
  KBC {
    maxSize       :: Int,
    labelledRules :: Index (Labelled (Constrained (Rule f v))),
    queue         :: Queue (CP f v),
    considered    :: Set (Constrained (Equation f v)) }
  deriving Show

data CP f v =
  CP {
    cpSize     :: Integer,
    cpEquation :: Constrained (Equation f v) } deriving (Eq, Show)

instance (Sized f, Ord f, Ord v) => Ord (CP f v) where
  compare =
    comparing $ \(CP size (Constrained ctx (l :==: r))) ->
      (measure l, measure r, size)

instance (PrettyTerm f, Pretty v) => Pretty (CP f v) where
  pretty = pretty . cpEquation

report :: KBC f v -> String
report s = show r ++ " rewrite rules."
  where
    r = length (Index.elems (labelledRules s))

initialState :: Int -> KBC f v
initialState maxSize =
  KBC {
    maxSize       = maxSize,
    labelledRules = Index.empty,
    queue         = empty,
    considered    = Set.empty }

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

rules :: KBC f v -> Index (Constrained (Rule f v))
rules = Index.mapMonotonic peel id id . labelledRules

constrainedNormaliser ::
  (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) m (Context f v -> Tm f v -> Tm f v)
constrainedNormaliser = do
  rules <- gets rules
  return $ \ctx -> normaliseWith (anywhere (tryConstrainedRules ctx rules))

specificNormaliser ::
  (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) m (Set (Formula f v) -> Tm f v -> Tm f v)
specificNormaliser = do
  rules <- gets rules
  return $ \forms -> normaliseWith (anywhere (trySpecificRules forms rules))

normaliser ::
  (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  StateT (KBC f v) m (Tm f v -> Tm f v)
normaliser =
  gets (normaliseWith . anywhere . tryRules . rules)

complete ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) m ()
complete = do
  res <- dequeueM
  case res of
    Just (l1, l2, cp) -> do
      consider l1 l2 (cpEquation cp)
      complete
    Nothing ->
      return ()

newEquation ::
  (PrettyTerm f, Pretty v, Monad m, Sized f, Ord f, Ord v, Numbered v) =>
  Constrained (Equation f v) -> StateT (KBC f v) m ()
newEquation (Constrained ctx (t :==: u)) = do
  n <- gets maxSize
  let ctx' = toContext (formula ctx &&& Size (termSize t <== fromIntegral n) &&& Size (termSize u <== fromIntegral n))
  queueCPs noLabel (map unlabelled (split (Constrained ctx' (t :==: u))))

queueCPs ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> [Labelled (Constrained (Equation f v))] -> StateT (KBC f v) m ()
queueCPs l eqns = do
  norm <- normaliser
  n <- gets maxSize
  let cps = catMaybes (map (moveLabel . fmap (toCP norm)) eqns)
      cps' = [ cp | cp <- cps, cpSize (peel cp) <= fromIntegral n ]
  unless (null cps') (traceM (NewCPs (map peel cps')))
  enqueueM l cps'

toCP ::
  (Sized f, Ord f, Ord v, Numbered v, PrettyTerm f, Pretty v) =>
  (Tm f v -> Tm f v) ->
  Constrained (Equation f v) -> Maybe (CP f v)
toCP norm (Constrained ctx (l :==: r)) = do
  guard (l /= r)
  let l' :==: r' = order (norm l :==: norm r)
      ctx' = minimiseContext l' ctx
  guard (l' /= r')
  return (CP (modelSize l' (solved ctx')) (canonicalise (Constrained ctx' (l' :==: r'))))

consider ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> Label -> Constrained (Equation f v) -> StateT (KBC f v) m ()
consider l1 l2 eq@(Constrained ctx (t :==: u))
  | t == u = return ()
  | otherwise = do
      norm  <- normaliser
      snorm <- specificNormaliser
      cnorm <- constrainedNormaliser
      rules <- gets rules
      con   <- gets considered
      let eq' = order (norm t :==: norm u)
          ceq = canonicalise (Constrained ctx eq')
          f (Constrained ctx (l :==: r)) = Constrained ctx (r :==: l)
      traceM (Consider (Constrained ctx eq'))
      unless (ceq `Set.member` con || f ceq `Set.member` con) $ do
        modify (\s -> s { considered = Set.insert ceq (considered s) })
        case runWriter (evalStateT (consider' snorm rules) (Set.singleton (Constrained ctx eq'))) of
          (False, _) -> do
            forM_ (orientWith cnorm eq') $ \rule -> do
              traceM (NewRule (canonicalise rule))
              l <- addRule rule
              interreduce rule
              addCriticalPairs l rule
          (True, eqs) ->
            queueCPs l1 (map (Labelled l2) (usort eqs))

consider' ::
  (PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  (Set (Formula f v) -> Tm f v -> Tm f v) ->
  Index (Constrained (Rule f v)) ->
  StateT (Set (Constrained (Equation f v))) (Writer [Constrained (Equation f v)]) Bool
consider' snorm rules = do
  set <- get
  case Set.minView set of
    Nothing -> return True
    {-Just (Constrained ctx (t :==: u), set') | funny (formula ctx) -> return False
      where
        funny HeadIs{} = True
        funny Size{} = True
        funny (p :&: q) = funny p || funny q
        funny (p :|: q) = funny p || funny q
        funny _ = False-}
    Just (Constrained ctx (t :==: u), set') -> do
      let l :==: r = order (snorm Set.empty t :==: snorm Set.empty u)
          n = modelSize l (minimiseSolved l (solved ctx))
      put set'
      case bestCases snorm rules ctx (l :==: r) of
        Nothing -> return False
        Just FTrue -> consider' snorm rules
        Just form -> do
          let ctx'      = toContext (formula ctx &&& runM simplify (runM negFormula form))
              (eq:eqs1) = map canonicalise (split (Constrained (toContext (formula ctx &&& form)) (l :==: r)))
              eqs2      = map canonicalise (split (Constrained ctx' (l :==: r)))
              p (Constrained ctx (l :==: _)) =
                -- modelSize l (minimiseSolved l (solved ctx)) <= n
                True
              (here, there) = partition p (eqs1 ++ eqs2)
          modify (Set.delete eq . Set.union (Set.fromList here))
          lift (tell there)
          traceM (ConditionalJoin (Constrained ctx (l :==: r)) form)
          consider' snorm rules

orientWith ::
  (PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  (Context f v -> Tm f v -> Tm f v) ->
  Equation f v -> [Constrained (Rule f v)]
orientWith norm eq = orient eq >>= split >>= reduce
  where
    reduce (Constrained ctx (Rule t u)) = [Constrained ctx (Rule t u')]
      where
        u' = norm ctx u

bestCases ::
  (PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  (Set (Formula f v) -> Tm f v -> Tm f v) ->
  Index (Constrained (Rule f v)) ->
  Context f v -> Equation f v -> Maybe (Formula f v)
bestCases norm rules ctx (t :==: u) =
  findCases norm rules ctx (t :==: u) >>= fmap toForm . shrink
    where
      shrink (cases, forms) =
        msum (map try (shrinkSet (cases, forms))) `mplus`
        return cases
      try (cases, forms) = do
        guard (norm forms t == norm forms u)
        shrink (cases, forms)
      toForm s = foldr (&&&) FTrue (Set.toList s)
      shrinkSet (cases, forms) = [ (Set.delete x cases, Set.delete x forms) | x <- Set.toList cases ]

findCases ::
  (PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  (Set (Formula f v) -> Tm f v -> Tm f v) ->
  Index (Constrained (Rule f v)) ->
  Context f v -> Equation f v -> Maybe (Set (Formula f v), Set (Formula f v))
findCases norm rules ctx (t :==: u) = aux Set.empty Set.empty ctx t u
  where
    aux cases forms ctx t u
      | t == u || t' == u' = Just (cases, forms)
      | forms' /= forms = aux cases forms' ctx t u
      | otherwise = do
          (form, ctx') <- caseSplit rules ctx (t' :==: u')
          aux (Set.insert form cases) (Set.insert form forms) ctx' t' u'
      where
        forms' = Set.union forms (Set.fromList (impliedCases rules ctx (t' :==: u')))
        t' = norm forms t
        u' = norm forms u

impliedCases ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Constrained (Rule f v)) ->
  Context f v -> Equation f v -> [Formula f v]
impliedCases rules ctx (t :==: u) = do
  v <- subterms t ++ subterms u
  rule <- Index.lookup v rules
  let form = formula (context rule)
  guard (any (implies (solved ctx)) (mainSplits form))
  return form

caseSplit ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Constrained (Rule f v)) ->
  Context f v -> Equation f v -> Maybe (Formula f v, Context f v)
caseSplit rules ctx (t :==: u) =
  listToMaybe $ do
    v <- subterms t ++ subterms u
    rule <- Index.lookup v rules
    let form = formula (context rule)
        ctx' = toContext (mainSplit (form &&& formula ctx))
    guard (satisfiable (solved ctx'))
    traceM (CaseSplit ctx form (constrained rule))
    return (form, ctx')

addRule :: (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) m Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { labelledRules = Index.insert (Labelled l rule) (labelledRules s) })
  return l

deleteRule :: (Monad m, Sized f, Ord f, Ord v, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) m ()
deleteRule l rule =
  modify $ \s ->
    s { labelledRules = Index.delete (Labelled l rule) (labelledRules s),
        queue = deleteLabel l (queue s) }

data Reduction f v = Simplify (Constrained (Rule f v)) | Reorient (Constrained (Rule f v)) deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Reduction f v) where
  pretty (Simplify rule) = text "Simplify" <+> pretty rule
  pretty (Reorient rule) = text "Reorient" <+> pretty rule

interreduce :: (Monad m, PrettyTerm f, Ord f, Sized f, Ord v, Numbered v, Pretty v) => Constrained (Rule f v) -> StateT (KBC f v) m ()
interreduce new = do
  rules <- gets (Index.elems . labelledRules)
  let reductions = catMaybes (map (moveLabel . fmap (reduceWith new)) rules)
  sequence_ [ traceM (Reduce red new) | red <- map peel reductions ]
  sequence_ [ simplifyRule l rule | Labelled l (Simplify rule) <- reductions ]
  sequence_ [ newEquation (Constrained (toContext FTrue) (unorient (constrained rule))) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduceWith :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Constrained (Rule f v) -> Constrained (Rule f v) -> Maybe (Reduction f v)
reduceWith new old
  | not (lhs (constrained new) `isInstanceOf` lhs (constrained old)) &&
    not (null (tryRule (context old) new (lhs (constrained old)))) =
      Just (Reorient old)
  | not (null (tryRule (context old) new (rhs (constrained old)))) =
      Just (Simplify old)
  | otherwise = Nothing

simplifyRule :: (Monad m, PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) m ()
simplifyRule l rule@(Constrained ctx (Rule lhs rhs)) = do
  norm <- constrainedNormaliser
  modify $ \s ->
    s {
      labelledRules =
         Index.insert (Labelled l (Constrained ctx (Rule lhs (norm ctx rhs))))
           (Index.delete (Labelled l rule) (labelledRules s)) }

addCriticalPairs :: (Monad m, PrettyTerm f, Ord f, Sized f, Ord v, Numbered v, Pretty v) => Label -> Constrained (Rule f v) -> StateT (KBC f v) m ()
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

criticalPairs :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Int -> Constrained (Rule f v) -> Constrained (Rule f v) -> [Constrained (Equation f v)]
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
        toContext (Size (termSize left <== fromIntegral n) &&& Size (termSize right <== fromIntegral n)) {- $
          substf (rename f . evalSubst sub . Left) (formula ctx1) &&&
          substf (rename f . evalSubst sub . Right) (formula ctx2) -}

  split (Constrained ctx (left :==: right))
