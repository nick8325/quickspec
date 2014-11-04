{-# LANGUAGE FlexibleInstances #-}
--module QuickSpec.Pruning.Completion where

import QuickSpec.Base hiding ((<>), nest, ($$), empty)
import QuickSpec.Term
--import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Utils
import qualified Data.Rewriting.CriticalPair as CP
import qualified Data.Rewriting.Rule as Rule
import qualified Data.Rewriting.Rules as Rules
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Data.Rewriting.Substitution.Ops as Subst
import Data.Either
import Control.Monad
import Control.Monad.State.Strict
import Data.Maybe
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map as Map
import Data.List
import Debug.Trace
import Data.Ord
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)

instance PrettyTerm String
type PruningTerm = Tm PruningConstant PruningVariable
type PruningConstant = String
type PruningVariable = Int
instance Sized [Char] where funSize _ = 1
v :: Int -> PruningTerm
v = Var
x = v 0
y = v 1
z = v 2

plus t u = Fun "plus" [t, u]
times t u = Fun "times" [t, u]
zero = Fun "zero" []
one = Fun "one" []
eqs = [
  plus x y === plus y x,
  plus zero x === x,
  --plus x (plus y z) === plus y (plus x z),
  plus x (plus y z) === plus (plus x y) z,
  times x y === times y x,
  times zero x === zero,
  times one x === x,
  --times x (times y z) === times y (times x z),
  times x (times y z) === times (times x y) z,
  times x (plus y z) === plus (times x y) (times x z)]

type T = StateT Completion
data Completion =
  Completion {
    maxSize   :: Int,
    sizeDelta :: Int,
    rules     :: Index Rule,
    queue     :: Set Equation }
  deriving Show

initialState = Completion 0 1 Index.empty Set.empty

data Equation = PruningTerm :==: PruningTerm deriving (Eq, Show)
type Rule = RuleOf PruningTerm
type PruningCP = CPOf PruningTerm

(===) :: PruningTerm -> PruningTerm -> Equation
x === y
  | Measure x < Measure y = y :==: x
  | otherwise = x :==: y

instance Ord Equation where
  compare = comparing (\(l :==: r) -> (Measure l, Measure r))

orient :: Equation -> Maybe Rule
orient eq@(l :==: r) =
  case orientTerms l r of
    Just LT -> Just (Rule.Rule r l)
    Just GT -> Just (Rule.Rule l r)
    _       -> Nothing

criticalPairs :: Rule -> Rule -> [Equation]
criticalPairs r1 r2 = do
  cp <- CP.cps [r1] [r2]
  let top = CP.top cp
      left = CP.left cp
      right = CP.right cp

  -- XXX for equations
  -- unless (oriented [r1]) $ guard (not (top `simplerThan` left))
  -- unless (oriented [r2]) $ guard (not (top `simplerThan` right))

  let (left', right') = canonicalise (left, right)
      f (Left x) = x
      f (Right x) = x
  return (rename f left' === rename f right')

type Strategy f v = Tm f v -> [Tm f v]

normaliseWith :: Strategy f v -> Tm f v -> Tm f v
normaliseWith strat t =
  case strat t of
    [] -> t
    (r:_) -> normaliseWith strat r

anywhere :: Strategy f v -> Strategy f v
anywhere strat t = strat t ++ nested (anywhere strat) t

nested :: Strategy f v -> Strategy f v
nested strat Var{} = []
nested strat (Fun f xs) = map (Fun f) (combine xs (map strat xs))
  where
    combine [] [] = []
    combine (x:xs) (ys:yss) =
      [ y:xs | y <- ys ] ++ [ x:zs | zs <- combine xs yss ]

rewrite :: Index Rule -> Strategy PruningConstant PruningVariable
rewrite rules t = map Rule.rhs (Index.lookup t rules)

normalise :: Monad m => PruningTerm -> StateT Completion m PruningTerm
normalise t = do
  Completion { rules = rules } <- get
  return (normaliseWith (anywhere (rewrite rules)) t)

newEquation :: Monad m => Equation -> StateT Completion m ()
newEquation (l :==: r) = do
  l <- normalise l
  r <- normalise r
  unless (l == r) $
    modify (\s -> s { queue = Set.insert (l === r) (queue s) })

complete :: Monad m => StateT Completion m ()
complete = do
  Completion { maxSize = maxSize, queue = queue } <- get
  case Set.minView queue of
    Just (eq, queue') -> do
      modify (\s -> s { queue = queue' })
      consider eq
      complete
    _ -> return ()

consider :: Monad m => Equation -> StateT Completion m ()
consider (l :==: r) = do
  l <- normalise l
  r <- normalise r
  maxSize <- gets maxSize
  when (size l <= maxSize && size r <= maxSize) $
    case fmap canonicalise (orient (l :==: r)) of
      Nothing -> return ()
      Just rule -> do
        trace (show (pretty (size l) <+> pretty rule)) $ return ()
        modify (\s -> s { rules = Index.insert rule (rules s) })
        interreduce rule
        addCriticalPairs rule

addCriticalPairs :: Monad m => Rule -> StateT Completion m ()
addCriticalPairs rule = do
  Completion { rules = rules } <- get
  mapM_ newEquation (concat [ criticalPairs rule rule' | rule' <- Index.elems rules ])
  mapM_ newEquation (concat [ criticalPairs rule' rule | rule' <- Index.elems rules ])

data Reduction = Simplify Rule | Reorient Rule

instance Show Reduction where
  show (Simplify r) = "simplify rhs of " ++ prettyShow r
  show (Reorient r) = "simplify lhs of " ++ prettyShow r

interreduce :: Monad m => Rule -> StateT Completion m ()
interreduce rule = do
  Completion { rules = rs } <- get
  let reductions = catMaybes (map (interreduction rule) (Index.elems rs))
  sequence_ [ traceShow r (return ()) | r <- reductions ]
  sequence_ [ simplifyRule r | Simplify r <- reductions ]
  sequence_ [ newEquation (Rule.lhs r :==: Rule.rhs r) | Reorient r <- reductions ]
  sequence_ [ deleteRule r | Reorient r <- reductions ]

interreduction :: Rule -> Rule -> Maybe Reduction
interreduction new old
  | not (Rule.lhs new `isInstanceOf` Rule.lhs old) &&
    not (null (Rules.fullRewrite [new] (Rule.lhs old))) =
      Just (Reorient old)
  | not (null (Rules.fullRewrite [new] (Rule.rhs old))) =
      Just (Simplify old)
  | otherwise = Nothing

addRule :: Monad m => Rule -> StateT Completion m ()
addRule r = modify (\s -> s { rules = Index.insert r (rules s) })

deleteRule :: Monad m => Rule -> StateT Completion m ()
deleteRule r = modify (\s -> s { rules = Index.delete r (rules s) })

simplifyRule :: Monad m => Rule -> StateT Completion m ()
simplifyRule r = do
  rhs' <- normalise (Rule.rhs r)
  let r' = r { Rule.rhs = rhs' }
  deleteRule r
  addRule r'

main = do
  let rs = reverse (Index.elems (rules (execState (mapM_ newEquation eqs >> complete) initialState { maxSize = 15 })))
  print (length rs)
  mapM_ prettyPrint rs

newAxiom :: Monad m => PropOf PruningTerm -> StateT Completion m ()
newAxiom ([] :=>: (t :=: u)) = do
  Completion { maxSize = maxSize, sizeDelta = sizeDelta } <- get
  let newSize = size t `max` size u
  when (newSize > maxSize) $
    modify (\s -> s { maxSize = newSize + sizeDelta })
  newEquation (t :==: u)
  complete
