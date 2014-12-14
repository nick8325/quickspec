-- Knuth-Bendix completion, up to an adjustable size limit.
-- Doesn't deal with unorientable equations but keeps them around
-- for a higher level to use.

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
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.Rewriting.CriticalPair as CP
import Data.Rewriting.Rule(Rule(..))
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Debug.Trace

data Event f v =
    NewRule (Constrained (Rule f v))
  | NewCPs [CP f v]
  | Consider (Constrained (Equation f v))
  | CaseSplit (Context f v) (Formula f v) (Rule f v)
  | ConditionalJoin (Constrained (Equation f v)) (Formula f v)
  | Pause (Constrained (Equation f v))
  | Reduce (Reduction f v) (Constrained (Rule f v))
  | Complete
  | Unpausing

traceM :: (Monad m, PrettyTerm f, Pretty v) => Event f v -> m ()
traceM (NewRule rule) = traceIf True (hang (text "New rule") 2 (pretty rule))
traceM (NewCPs cps) = traceIf True (hang (text "New critical pairs") 2 (pretty cps))
traceM (Consider eq) = traceIf True (hang (text "Considering") 2 (pretty eq))
traceM (CaseSplit ctx form rule) = traceIf False (sep [text "Splitting on", nest 2 (pretty form), text "in", nest 2 (pretty ctx), text "to apply", nest 2 (pretty rule)])
traceM (ConditionalJoin eq form) = traceIf True (sep [text "Conditionally joined", nest 2 (pretty eq), text "assuming", nest 2 (pretty form)])
traceM (Pause eqn) = traceIf False (hang (text "Pausing equation") 2 (pretty eqn))
traceM (Reduce red rule) = traceIf False (sep [pretty red, nest 2 (text "using"), nest 2 (pretty rule)])
traceM Complete = traceIf False (text "Finished completion")
traceM Unpausing = traceIf False (text "Found rules to unpause")
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
      (measure l, measure r, size)

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
  let resumable (Constrained ctx eq) = isJust (caseSplit rules ctx eq)
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
  unless (null cps1) (traceM (NewCPs (map peel cps1)))
  enqueueM l cps1
  sequence_ [ pause eq | Labelled _ (CP _ eq) <- cps2 ]

toCP ::
  (Sized f, Ord f, Ord v, Numbered v, PrettyTerm f, Pretty v) =>
  (Context f v -> Tm f v -> Tm f v) ->
  Constrained (Equation f v) -> Maybe (CP f v)
toCP norm (Constrained ctx (l :==: r)) = do
  guard (l /= r)
  let l' = norm ctx l
      r' = norm ctx r
      eqn' = order (l' :==: r')
  guard (l' /= r')
  return (CP (minSize (solved ctx) l' `max` minSize (solved ctx) r') (canonicalise (Constrained ctx eqn')))

consider ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Label -> Label -> Constrained (Equation f v) -> StateT (KBC f v) m ()
consider l1 l2 eq@(Constrained ctx (t :==: u))
  | t == u = return ()
  | otherwise = do
      traceM (Consider eq)
      norm  <- normaliser
      rules <- gets rules
      let t' = norm ctx t
          u' = norm ctx u
      case bestCases norm rules ctx (t' :==: u') of
        Nothing -> do
          forM_ (orientWith norm (t' :==: u')) $ \rule -> do
            traceM (NewRule (canonicalise rule))
            l <- addRule rule
            interreduce rule
            addCriticalPairs l rule
        Just FTrue -> return ()
        Just form -> do
          let ctx1     = toContext (formula ctx &&& runM simplify form)
              ctx2     = toContext (formula ctx &&& runM simplify (runM negFormula form))
              (_:eqs1) = split (Constrained ctx1 (t' :==: u'))
              eqs2     = split (Constrained ctx2 (t' :==: u'))
          traceM (ConditionalJoin (Constrained ctx (t' :==: u')) form)
          queueCPs l1 (map (Labelled l2) (eqs1 ++ eqs2))

orientWith ::
  (PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  (Context f v -> Tm f v -> Tm f v) ->
  Equation f v -> [Constrained (Rule f v)]
orientWith norm eq = orient eq >>= split >>= reduce
  where
    reduce (Constrained ctx (Rule t u))
      | t == t' = [Constrained ctx (Rule t u')]
      | otherwise = orientWith norm (t' :==: u')
      where
        t' = norm ctx t
        u' = norm ctx u

bestCases ::
  (PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  (Context f v -> Tm f v -> Tm f v) ->
  Index (Labelled (Constrained (Rule f v))) ->
  Context f v -> Equation f v -> Maybe (Formula f v)
bestCases norm rules ctx (t :==: u) =
  findCases norm rules ctx (t :==: u) >>= shrink
    where
      shrink form = msum (map try (shrinkFormula form)) `mplus` return form
      try form = do
        let form' = mainSplit (form &&& formula ctx)
            ctx' = toContext form'
        guard (norm ctx' t == norm ctx' u)
        shrink form

findCases ::
  (PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  (Context f v -> Tm f v -> Tm f v) ->
  Index (Labelled (Constrained (Rule f v))) ->
  Context f v -> Equation f v -> Maybe (Formula f v)
findCases norm rules ctx (t :==: u)
  | t' == u' = Just FTrue
  | otherwise = do
      (form, ctx') <- caseSplit rules ctx (t' :==: u')
      fmap (form &&&) (findCases norm rules ctx' (t' :==: u'))
  where
    t' = norm ctx t
    u' = norm ctx u

caseSplit ::
  (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) =>
  Index (Labelled (Constrained (Rule f v))) ->
  Context f v -> Equation f v -> Maybe (Formula f v, Context f v)
caseSplit rules ctx (t :==: u) =
  listToMaybe $ do
    v <- subterms t ++ subterms u
    rule <- map peel (Index.lookup v rules)
    let form = formula (context rule)
        ctx' = toContext (mainSplit (form &&& formula ctx))
    guard (satisfiable (solved ctx'))
    traceM (CaseSplit ctx form (constrained rule))
    return (form, ctx')

shrinkFormula :: Formula f v -> [Formula f v]
shrinkFormula (p :&: q) =
  [p, q] ++
  [p &&& q' | q' <- shrinkFormula q] ++
  [p' &&& q | p' <- shrinkFormula p]
shrinkFormula (p :|: q) =
  [p ||| q' | q' <- shrinkFormula q] ++
  [p' ||| q | p' <- shrinkFormula p]
shrinkFormula (Less (Fun _ ts) u) =
  FTrue:[Less t u | t <- ts]
shrinkFormula FTrue = []
shrinkFormula _ = [FTrue]

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
  sequence_ [ newEquation (Constrained (toContext FTrue) (unorient (constrained rule))) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduce :: (PrettyTerm f, Pretty v, Sized f, Ord f, Ord v, Numbered v) => Constrained (Rule f v) -> Constrained (Rule f v) -> Maybe (Reduction f v)
reduce new old
  | not (lhs (constrained new) `isInstanceOf` lhs (constrained old)) &&
    not (null (tryRule (context old) new (lhs (constrained old)))) =
      Just (Reorient old)
  | not (null (tryRule (context old) new (rhs (constrained old)))) =
      Just (Simplify old)
  | otherwise = Nothing

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
        toContext $
          substf (rename f . evalSubst sub . Left) (formula ctx1) &&&
          substf (rename f . evalSubst sub . Right) (formula ctx2)

  split (Constrained ctx (left :==: right))
