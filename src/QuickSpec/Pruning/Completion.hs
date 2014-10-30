{-# LANGUAGE FlexibleInstances #-}
-- https://hal.inria.fr/inria-00075875/document
module QuickSpec.Pruning.Completion where

import QuickSpec.Base hiding ((<>), nest)
import QuickSpec.Term
--import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Utils
import qualified Data.Rewriting.CriticalPair as CP
import qualified Data.Rewriting.Rule as Rule
import qualified Data.Rewriting.Rules as Rules
import Data.Rewriting.Rules(Strategy)
import qualified Data.Rewriting.Rules.Rewrite as Rules
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
import Data.Ord

type PruningTerm = Tm PruningConstant PruningVariable
type PruningConstant = String
type PruningVariable = Int
instance Sized [Char] where funSize _ = 1
v :: Int -> PruningTerm
v = Var
x = v 0
y = v 1
z = v 2
op t u = Fun "+" [t, u]
inv t = Fun "-" [t]
ident = Fun "z" []

eqs = [
  (ident `op` x) === x,
  (inv x `op` x) === ident,
  (x `op` (y `op` z)) === ((x `op` y) `op` z)]

data Equation = PruningTerm :==: PruningTerm deriving (Eq, Show)
type Rule = Rule.Rule PruningConstant PruningVariable
type PruningCP = CP.CP PruningConstant PruningVariable PruningVariable

equationSize :: Equation -> Int
equationSize (l :==: _r) = size l

(===) :: Ord v => Tm PruningConstant v -> Tm PruningConstant v -> Equation
x === y | Measure x < Measure y = y === x
x === y = x' :==: y'
  where
    -- Rename variables in a nice way
    vs = nub (vars x ++ vars y)
    sub' = Subst.fromMap (Map.fromList (zip vs (map Var [0..])))
    Just x' = Subst.gApply sub' x
    Just y' = Subst.gApply sub' y

instance Ord Equation where
  compare = comparing (\(l :==: r) -> (Measure l, Measure r))

type T = StateT Completion
data Completion =
  Completion {
    maxSize   :: Int,
    sizeDelta :: Int,
    rules     :: [Rule],
    equations :: Set Equation,
    queue     :: Set Equation }
  deriving Show

initialState = Completion 0 1 [] Set.empty Set.empty

class Ruling a where
  rule :: a -> Rule
  oriented :: proxy a -> Bool

rewrite :: Ruling a => [a] -> Strategy PruningConstant PruningVariable PruningVariable
rewrite rs
  | oriented rs = Rules.fullRewrite (map rule rs)
  | otherwise = ordered (Rules.fullRewrite (map rule rs))

instance Ruling Rule where
  rule = id
  oriented _ = True

data DirectedEquation =
    LeftToRight { undirect ::  Equation }
  | RightToLeft { undirect :: Equation }

instance Ruling DirectedEquation where
  rule (LeftToRight (l :==: r)) = Rule.Rule l r
  rule (RightToLeft (l :==: r)) = Rule.Rule r l
  oriented _ = False

direct :: Equation -> [DirectedEquation]
direct eq = [LeftToRight eq, RightToLeft eq]

orient :: Equation -> Maybe Rule
orient eq@(l :==: r)
  | l `simplerThan` r = Just (Rule.Rule r l)
  | r `simplerThan` l = Just (Rule.Rule l r)
  | otherwise = Nothing

criticalPairs :: (Ruling a, Ruling b) => a -> b -> [Equation]
criticalPairs r1 r2 = do
  cp <- CP.cps [rule r1] [rule r2]
  let sub = subst (CP.subst cp)
      top = sub (CP.top cp)
      left = sub (CP.left cp)
      right = sub (CP.right cp)

  unless (oriented [r1]) $ guard (not (top `simplerThan` left))
  unless (oriented [r2]) $ guard (not (top `simplerThan` right))
  return (left === right)

normalise :: Strategy f v v -> Tm f v -> Tm f v
normalise strat t =
  case strat t of
    [] -> t
    (r:_) -> normalise strat (Rules.result r)

choice :: Strategy f v v' -> Strategy f v v' -> Strategy f v v'
choice s1 s2 t = s1 t ++ s2 t

ordered :: (Sized f, Ord f, Ord v) => Strategy f v v -> Strategy f v v
ordered s1 t = do
  r <- s1 t
  guard (Rules.result r `simplerThan` t)
  return r

reduceEquations :: Set Equation -> Strategy PruningConstant PruningVariable PruningVariable
reduceEquations eqs = rewrite (concatMap direct (Set.toList eqs))

normaliseEquation :: Monad m => Equation -> StateT Completion m Equation
normaliseEquation eq = do
  Completion { rules = rules, equations = equations, maxSize = maxSize } <- get
  let strat = choice (rewrite rules) (reduceEquations equations)
  return (normaliseEquationWith strat eq)

normaliseEquationWith :: Strategy PruningConstant PruningVariable PruningVariable -> Equation -> Equation
normaliseEquationWith strat (l :==: r) = l' === r'
  where
    l' = normalise strat l
    r' = normalise strat r

newEquation :: Monad m => Equation -> StateT Completion m ()
newEquation eq = do
  l :==: r <- normaliseEquation eq
  if l == r then return ()
    else modify (\s -> s { queue = Set.insert (l :==: r) (queue s) })

addEquation :: Monad m => Equation -> StateT Completion m ()
addEquation eq = do
  l :==: r <- normaliseEquation eq
  if l == r then return () else
    case orient (l :==: r) of
      Just rule -> addRule rule
      Nothing -> modify (\s -> s { equations = Set.insert (l :==: r) (equations s) })

addRule :: Monad m => Rule -> StateT Completion m ()
addRule r = do
  simplifyQueueWith r
  simplifyRulesWith r
  simplifyEquationsWith r
  modify (\s -> s { rules = r:rules s })
  rs <- gets rules
  let cps = usort (concat [ criticalPairs r r' ++ criticalPairs r' r | r' <- rs ])
  mapM_ newEquation cps

simplifyRulesWith :: (Monad m, Ruling a) => a -> StateT Completion m ()
simplifyRulesWith r = do
  Completion { rules = rules } <- get
  let (rules', eqs') = partitionEithers (map (simplifyRuleWith r) rules)
  modify (\s -> s { rules = rules',
                    queue = Set.union (queue s) (Set.fromList eqs') })

simplifyEquationsWith :: (Monad m, Ruling a) => a -> StateT Completion m ()
simplifyEquationsWith r = do
  Completion { equations = eqs } <- get
  modify (\s -> s { equations = Set.empty })
  mapM_ newEquation (Set.toList eqs)

simplifyQueueWith :: (Monad m, Ruling a) => a -> StateT Completion m ()
simplifyQueueWith r =
  modify $
    \s -> s {
      queue =
        Set.fromList
          (map (normaliseEquationWith (rewrite [r]))
            (Set.toList (queue s))) }

simplifyRuleWith :: Ruling a => a -> Rule -> Either Rule Equation
simplifyRuleWith r (Rule.Rule lhs rhs)
  | lhs == lhs' && rhs == rhs' = Left (Rule.Rule lhs rhs)
  | otherwise = Right (lhs' === rhs')
  where
    lhs' = normalise (rewrite [r]) lhs
    rhs' = normalise (rewrite [r]) rhs

complete :: Monad m => StateT Completion m ()
complete = do
  Completion { maxSize = maxSize, queue = queue } <- get
  case Set.minView queue of
    Just (eq@(l:==:r), queue') | equationSize eq <= maxSize -> do
      modify (\s -> s { queue = queue' })
      addEquation eq
      complete
    _ -> return ()

newAxiom :: Monad m => PropOf PruningTerm -> StateT Completion m ()
newAxiom ([] :=>: (t :=: u)) = do
  Completion { maxSize = maxSize, sizeDelta = sizeDelta } <- get
  let newSize = size t `max` size u
  when (newSize > maxSize) $
    modify (\s -> s { maxSize = newSize + sizeDelta })
  newEquation (t === u)
  complete
