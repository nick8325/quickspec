{-# LANGUAGE FlexibleInstances #-}
-- https://hal.inria.fr/inria-00075875/document
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
import qualified QuickSpec.Pruning.RuleSet as RuleSet
import QuickSpec.Pruning.RuleSet(RuleSet)

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
    rules     :: RuleSet PruningConstant PruningVariable,
    queue     :: Set Equation }
  deriving Show

initialState = Completion 0 1 RuleSet.empty Set.empty

data Equation = PruningTerm :==: PruningTerm deriving (Eq, Show)
type Rule = Rule.Rule PruningConstant PruningVariable
type PruningCP = CP.CP PruningConstant PruningVariable PruningVariable

(===) :: PruningTerm -> PruningTerm -> Equation
x === y
  | Measure x < Measure y = y :==: x
  | otherwise = x :==: y

renameVars x y = x' :==: y'
  where
    vs = nub (vars x ++ vars y)
    sub' = Subst.fromMap (Map.fromList (zip vs (map Var [0..])))
    Just x' = Subst.gApply sub' x
    Just y' = Subst.gApply sub' y

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
  let sub = subst (CP.subst cp)
      top = sub (CP.top cp)
      --left = sub (CP.left cp)
      --right = sub (CP.right cp)
      left = CP.left cp
      right = CP.right cp

  -- XXX for equations
  -- unless (oriented [r1]) $ guard (not (top `simplerThan` left))
  -- unless (oriented [r2]) $ guard (not (top `simplerThan` right))
  return (renameVars left right)

type Strategy f v = Tm f v -> [Tm f v]

normalise :: Strategy f v -> Tm f v -> Tm f v
normalise strat t =
  case strat t of
    [] -> t
    (r:_) -> normalise strat r

anywhere :: Strategy f v -> Strategy f v
anywhere strat t = strat t ++ nested (anywhere strat) t

nested :: Strategy f v -> Strategy f v
nested strat Var{} = []
nested strat (Fun f xs) = map (Fun f) (combine xs (map strat xs))
  where
    combine [] [] = []
    combine (x:xs) (ys:yss) =
      [ y:xs | y <- ys ] ++ [ x:zs | zs <- combine xs yss ]

rewrite :: (Ord f, Ord v) => RuleSet f v -> Strategy f v
rewrite rules t = fmap Rule.rhs (RuleSet.match t rules)

normaliseM :: Monad m => PruningTerm -> StateT Completion m PruningTerm
normaliseM t = do
  Completion { rules = rules } <- get
  return (normalise (anywhere (rewrite rules)) t)

newEquation :: Monad m => Equation -> StateT Completion m ()
newEquation (l :==: r) = do
  l <- normaliseM l
  r <- normaliseM r
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
  l <- normaliseM l
  r <- normaliseM r
  maxSize <- gets maxSize
  when (size l <= maxSize && size r <= maxSize) $
    case orient (l :==: r) of
      Nothing -> return ()
      Just rule@(Rule.Rule l r) -> do
        -- HACK rename variables
        let l' :==: r' = renameVars l r
            rule = Rule.Rule l' r'
        trace (show (pretty (size l) <+> pretty rule)) $ return ()
        modify (\s -> s { rules = RuleSet.insert rule (rules s) })
        interreduce rule
        addCriticalPairs rule

addCriticalPairs :: Monad m => Rule -> StateT Completion m ()
addCriticalPairs rule = do
  Completion { rules = rules } <- get
  mapM_ newEquation (concat [ criticalPairs rule rule' | rule' <- RuleSet.elems rules ])
  mapM_ newEquation (concat [ criticalPairs rule' rule | rule' <- RuleSet.elems rules ])

data Reduction = Simplify Rule | Reorient Rule

instance Show Reduction where
  show (Simplify r) = "simplify rhs of " ++ prettyShow r
  show (Reorient r) = "simplify lhs of " ++ prettyShow r

interreduce :: Monad m => Rule -> StateT Completion m ()
interreduce rule = do
  Completion { rules = rs } <- get
  let reductions = catMaybes (map (interreduction rule) (RuleSet.elems rs))
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
addRule r = modify (\s -> s { rules = RuleSet.insert r (rules s) })

deleteRule :: Monad m => Rule -> StateT Completion m ()
deleteRule r = modify (\s -> s { rules = RuleSet.delete r (rules s) })

simplifyRule :: Monad m => Rule -> StateT Completion m ()
simplifyRule r = do
  rhs' <- normaliseM (Rule.rhs r)
  let r' = r { Rule.rhs = rhs' }
  deleteRule r
  addRule r'

main = do
  let rs = reverse (RuleSet.elems (rules (execState (mapM_ newEquation eqs >> complete) initialState { maxSize = 15 })))
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
