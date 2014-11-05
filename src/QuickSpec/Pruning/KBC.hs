-- Knuth-Bendix completion, up to an adjustable size limit.
-- No support for unorientable equations, but it will save them
-- and try to simplify them in case they become orientable later.
module QuickSpec.Pruning.KBC where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Utils
import QuickSpec.Pruning.Queue hiding (queue)
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import QuickSpec.Pruning.Equation
import qualified QuickSpec.Pruning.Equations as Equations
import QuickSpec.Pruning.Equations(Equations)
import QuickSpec.Pruning.Rewrite
import Data.Rewriting.Rule hiding (rename, isInstanceOf)
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Rewriting.CriticalPair as CP
import Data.Ord
import Data.Maybe
import Debug.Trace

data KBC f v =
  KBC {
    maxSize   :: Int,
    rules     :: Index (Labelled (Rule f v)),
    queue     :: Queue (QueueEquation f v),
    paused    :: Set (Equation f v) }
  deriving Show

newtype QueueEquation f v =
  QueueEquation { unQueueEquation :: Rule f v } deriving (Eq, Show)
instance (Sized f, Ord f, Ord v) => Ord (QueueEquation f v) where
  compare = comparing (measureRule . unQueueEquation)
    where
      measureRule (Rule lhs rhs) = (Measure lhs, Measure rhs)

toQueueEquation :: (Sized f, Ord f, Ord v) => Equation f v -> QueueEquation f v
toQueueEquation eqn = QueueEquation (order eqn)

fromQueueEquation :: QueueEquation f v -> Equation f v
fromQueueEquation (QueueEquation rule) = unorient rule

initialState :: Int -> KBC f v
initialState maxSize =
  KBC {
    maxSize   = maxSize,
    rules     = Index.empty,
    queue     = empty,
    paused    = Set.empty }

enqueueM ::
  (Monad m, Sized f, Ord f, Ord v) =>
  Label -> [Labelled (Equation f v)] -> StateT (KBC f v) m ()
enqueueM l eqns =
  modify (\s -> s { queue = enqueue l (map (fmap toQueueEquation) eqns) (queue s) })

dequeueM ::
  (Monad m, Sized f, Ord f, Ord v) =>
  StateT (KBC f v) m (Maybe (Equation f v))
dequeueM =
  state $ \s ->
    case dequeue (queue s) of
      Nothing -> (Nothing, s)
      Just (x, q) ->
        (Just (fromQueueEquation (peel x)), s { queue = q })

newLabelM :: Monad m => StateT (KBC f v) m Label
newLabelM =
  state $ \s ->
    case newLabel (queue s) of
      (l, q) -> (l, s { queue = q })

pause :: (Monad m, Sized f, Ord f, Ord v) => Equation f v -> StateT (KBC f v) m ()
pause eqn = modify (\s -> s { paused = Set.insert eqn (paused s) })

normaliser ::
  (Monad m, Ord f, Ord v) => StateT (KBC f v) m (Tm f v -> Tm f v)
normaliser = gets (normaliseWith . anywhere . tryLabelledRules . rules)

tryLabelledRules :: (Ord f, Ord v) => Index (Labelled (Rule f v)) -> Strategy f v
tryLabelledRules rules t = map (rhs . peel) (Index.lookup t rules)

complete ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) m ()
complete = do
  res <- dequeueM
  case res of
    Just eqn -> do
      consider eqn
      complete
    Nothing -> unpause

unpause ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  StateT (KBC f v) m ()
unpause = do
  paused  <- gets paused
  reduce  <- gets (anywhere . tryLabelledRules . rules)
  norm    <- normaliser
  let resumable (t :==: u) = reduce t /= [] || reduce u /= []
      (resumed, paused') = Set.partition resumable paused
  when (not (Set.null resumed)) $ do
    mapM_ newEquation (Set.toList resumed)
    modify (\s -> s { paused = paused' })
    complete

increaseSize ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Int -> StateT (KBC f v) m ()
increaseSize n = do
  m <- gets maxSize
  when (n > m) $ do
    modify (\s -> s { maxSize = n })
    unpause

newEquation ::
  (Monad m, Sized f, Ord f, Ord v) =>
  Equation f v -> StateT (KBC f v) m ()
newEquation eqn = queueCPs noLabel [unlabelled eqn]

queueCPs ::
  (Monad m, Sized f, Ord f, Ord v) =>
  Label -> [Labelled (Equation f v)] -> StateT (KBC f v) m ()
queueCPs l eqns = do
  norm   <- normaliser
  enqueueM l (filter (not . trivial . peel) (map (fmap (bothSides norm)) eqns))

consider ::
  (Monad m, PrettyTerm f, Sized f, Ord f, Ord v, Numbered v, Pretty v) =>
  Equation f v -> StateT (KBC f v) m ()
consider eqn = do
  maxSize <- gets maxSize
  norm    <- normaliser
  let eqn' = bothSides norm eqn
  unless (trivial eqn') $
    if equationSize eqn' >= maxSize
      then pause eqn'
      else
        case orient eqn' of
          Just rule -> do
            l <- addRule rule
            interreduce rule
            addCriticalPairs l rule
          Nothing -> pause eqn'

addRule :: (Monad m, Ord f, Ord v, Numbered v) => Rule f v -> StateT (KBC f v) m Label
addRule rule = do
  l <- newLabelM
  modify (\s -> s { rules = Index.insert (Labelled l rule) (rules s) })
  return l

deleteRule :: (Monad m, Ord f, Ord v, Numbered v) => Label -> Rule f v -> StateT (KBC f v) m ()
deleteRule l rule =
  modify $ \s ->
    s { rules = Index.delete (Labelled l rule) (rules s),
        queue = deleteLabel l (queue s) }

data Reduction f v = Simplify (Rule f v) | Reorient (Rule f v)

interreduce :: (Monad m, Ord f, Sized f, Ord v, Numbered v) => Rule f v -> StateT (KBC f v) m ()
interreduce new = do
  rules <- gets (Index.elems . rules)
  let reductions = catMaybes (map (moveLabel . fmap (reduce new)) rules)
  sequence_ [ simplifyRule l rule | Labelled l (Simplify rule) <- reductions ]
  sequence_ [ newEquation (unorient rule) | Reorient rule <- map peel reductions ]
  sequence_ [ deleteRule l rule | Labelled l (Reorient rule) <- reductions ]

reduce :: (Ord f, Ord v) => Rule f v -> Rule f v -> Maybe (Reduction f v)
reduce new@(Rule l r) old
  | not (l `isInstanceOf` lhs old) &&
    not (null (tryRule new (lhs old))) =
      Just (Reorient old)
  | not (null (tryRule new (rhs old))) =
      Just (Simplify old)
  | otherwise = Nothing

simplifyRule :: (Monad m, Ord f, Ord v, Numbered v) => Label -> Rule f v -> StateT (KBC f v) m ()
simplifyRule l rule = do
  norm <- normaliser
  modify $ \s ->
    s{
      rules =
         Index.insert (Labelled l rule { rhs = norm (rhs rule) })
           (Index.delete (Labelled l rule) (rules s)) }

addCriticalPairs :: (Monad m, Ord f, Sized f, Ord v, Numbered v) => Label -> Rule f v -> StateT (KBC f v) m ()
addCriticalPairs l new = do
  rules <- gets rules
  queueCPs l $
    [ Labelled l' cp
    | Labelled l' old <- Index.elems rules,
      cp <- usort (criticalPairs new old ++ criticalPairs old new) ]

criticalPairs :: (Ord f, Ord v, Numbered v) => Rule f v -> Rule f v -> [Equation f v]
criticalPairs r1 r2 = do
  cp <- CP.cps [r1] [r2]
  let left = CP.left cp
      right = CP.right cp

  let (left', right') = canonicalise (left, right)
      f (Left x) = x
      f (Right x) = x
  return (rename f left' :==: rename f right')

