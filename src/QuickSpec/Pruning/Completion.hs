{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies, DeriveFunctor #-}
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
import Data.List hiding (delete)
import Debug.Trace
import Data.Ord
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index(Index)
import QuickSpec.Pruning.Equation
import qualified Data.PQueue.Min as Queue
import Data.PQueue.Min(MinQueue)
import Control.Applicative

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
  plus x y :==: plus y x,
  plus zero x :==: x,
  plus x (plus y z) :==: plus y (plus x z),
  --plus x (plus y z) :==: plus (plus x y) z,
  times x y :==: times y x,
  times zero x :==: zero,
  times one x :==: x,
  times x (times y z) :==: times y (times x z),
--  times x (times y z) :==: times (times x y) z,
  times x (plus y z) :==: plus (times x y) (times x z)]

type Eqn = EquationOf PruningTerm
type Rule = RuleOf PruningTerm
type PruningCP = CPOf PruningTerm

type T = StateT Completion
data Completion =
  Completion {
    maxSize   :: Int,
    maxEqSize :: Int,
    sizeDelta :: Int,
    nextLabel :: Label,
    labels    :: Set Label,
    rules     :: Index (Labelled Rule),
    left      :: Index (Labelled Rule),
    right     :: Index (Labelled Rule),
    queue     :: MinQueue (Labelled SubQueue),
    paused    :: [Eqn] }
  deriving Show

initialState =
  Completion {
    maxSize = 0,
    maxEqSize = 0,
    sizeDelta = 1,
    nextLabel = 1,
    labels = Set.singleton 0,
    rules = Index.empty,
    left = Index.empty,
    right = Index.empty,
    queue = Queue.empty,
    paused = [] }

newtype SubQueue = SubQueue (MinQueue (Labelled QueueEqn)) deriving Show
instance Eq SubQueue where SubQueue x == SubQueue y = Queue.getMin x == Queue.getMin y
instance Ord SubQueue where
  compare = comparing (\(SubQueue x) -> Queue.getMin x)

newtype QueueEqn = QueueEqn Rule deriving (Eq, Show)
instance Ord QueueEqn where
  compare = comparing (\(QueueEqn (Rule.Rule lhs rhs)) -> (Measure lhs, Measure rhs))

toQueueEqn :: Eqn -> QueueEqn
toQueueEqn eqn = QueueEqn (order eqn)

fromQueueEqn :: QueueEqn -> Eqn
fromQueueEqn (QueueEqn (Rule.Rule lhs rhs)) = lhs :==: rhs

enqueue :: Monad m => Label -> [Labelled Eqn] -> StateT Completion m ()
enqueue l [] = return ()
enqueue l eqns =
  modify (\s -> s { queue = Queue.insert q (queue s) })
  where
    q = Labelled l (SubQueue (Queue.fromList (map (fmap toQueueEqn) eqns)))

dequeue :: Monad m => StateT Completion m (Maybe Eqn)
dequeue = do
  queue  <- gets queue
  labels <- gets labels
  case dequeue1 labels queue of
    Nothing -> do
      modify (\s -> s { queue = Queue.empty })
      return Nothing
    Just (x, queue) -> do
      modify (\s -> s { queue = queue })
      return (Just x)
  where
    dequeue1 labels queue = do
      (Labelled l (SubQueue subqueue), queue) <- Queue.minView queue
      if l `Set.notMember` labels
        then dequeue1 labels queue
        else
          case dequeue2 labels subqueue of
            Nothing -> dequeue1 labels queue
            Just (x, subqueue) ->
              return (x, Queue.insert (Labelled l (SubQueue subqueue)) queue)
    dequeue2 labels subqueue = do
      (Labelled l x, subqueue) <- Queue.minView subqueue
      if l `Set.member` labels
        then return (fromQueueEqn x, subqueue)
        else dequeue2 labels subqueue

newtype Label = Label Int deriving (Eq, Ord, Num, Show)
data Labelled a = Labelled { labelOf :: Label, peel :: a } deriving (Show, Functor)
instance Eq a => Eq (Labelled a) where x == y = peel x == peel y
instance Ord a => Ord (Labelled a) where compare = comparing peel
instance Symbolic a => Symbolic (Labelled a) where
  type ConstantOf (Labelled a) = ConstantOf a
  type VariableOf (Labelled a) = VariableOf a
  termsDL = termsDL . peel
  substf sub (Labelled l x) = Labelled l (substf sub x)
instance Pretty a => Pretty (Labelled a) where pretty = pretty . peel

newLabel :: Monad m => StateT Completion m Label
newLabel = do
  Completion { nextLabel = n, labels = labels } <- get
  modify (\s -> s { nextLabel = n+1, labels = Set.insert n labels })
  return n

deleteLabel :: Monad m => Label -> StateT Completion m ()
deleteLabel l = modify (\s -> s { labels = Set.delete l (labels s) })

noLabel :: Label
noLabel = 0

unlabelled :: a -> Labelled a
unlabelled = Labelled noLabel

moveLabel :: Functor f => Labelled (f a) -> f (Labelled a)
moveLabel (Labelled l x) = fmap (Labelled l) x

data DirectedEqn = Rule Rule | Eqn Eqn deriving (Show, Eq, Ord)
instance Pretty DirectedEqn where
  pretty (Rule rule) = text "rule"     <+> pretty rule
  pretty (Eqn eqn)   = text "equation" <+> pretty eqn
instance Symbolic DirectedEqn where
  type ConstantOf DirectedEqn = PruningConstant
  type VariableOf DirectedEqn = PruningVariable
  termsDL (Rule rule) = termsDL rule
  termsDL (Eqn eqn)   = termsDL eqn
  substf sub (Rule rule) = Rule (substf sub rule)
  substf sub (Eqn eqn)   = Eqn  (substf sub eqn)

rule :: DirectedEqn -> Rule
rule (Rule x) = x
rule (Eqn (t :==: u)) = Rule.Rule t u

oriented :: DirectedEqn -> Bool
oriented Rule{} = True
oriented Eqn{} = False

direct :: Eqn -> [DirectedEqn]
direct (t :==: u) = [Eqn (t :==: u), Eqn (u :==: t)]

directedEqns :: Monad m => StateT Completion m [Labelled DirectedEqn]
directedEqns = do
  Completion { rules = rules, left = left, right = right } <- get
  return $
    map (fmap Rule) (Index.elems rules) ++
    map (fmap (Eqn . undirect)) (Index.elems left) ++
    map (fmap (Eqn . undirect)) (Index.elems right)

halfDirectedEqns :: Monad m => StateT Completion m [Labelled DirectedEqn]
halfDirectedEqns = do
  Completion { rules = rules, left = left } <- get
  return $
    map (fmap Rule) (Index.elems rules) ++
    map (fmap (Eqn . undirect)) (Index.elems left)

criticalPairs :: DirectedEqn -> DirectedEqn -> [Eqn]
criticalPairs r1 r2 = do
  cp <- CP.cps [rule r1] [rule r2]
  let top = CP.top cp
      left = CP.left cp
      right = CP.right cp

  unless (oriented r1) $ guard (not (top `simplerThan` left))
  unless (oriented r2) $ guard (not (top `simplerThan` right))

  let (left', right') = canonicalise (left, right)
      f (Left x) = x
      f (Right x) = x
  return (rename f left' :==: rename f right')

type Strategy = PruningTerm -> [PruningTerm]

normaliseWith :: Strategy -> PruningTerm -> PruningTerm
normaliseWith strat t =
  case strat t of
    [] -> t
    (r:_) -> normaliseWith strat r

anywhere :: Strategy -> Strategy
anywhere strat t = strat t ++ nested (anywhere strat) t

nested :: Strategy -> Strategy
nested strat Var{} = []
nested strat (Fun f xs) = map (Fun f) (combine xs (map strat xs))
  where
    combine [] [] = []
    combine (x:xs) (ys:yss) =
      [ y:xs | y <- ys ] ++ [ x:zs | zs <- combine xs yss ]

rewrite :: DirectedEqn -> Strategy
rewrite eqn t = do
  u <- map Rules.result (Rules.fullRewrite [rule eqn] t)
  unless (oriented eqn) $ guard (u `simplerThan` t)
  return u

rewriteRules :: Monad m => StateT Completion m Strategy
rewriteRules = do
  rules <- gets rules
  return . anywhere $ \t ->
    map (Rule.rhs . peel) (Index.lookup t rules)

rewriteEqn :: Monad m => StateT Completion m Strategy
rewriteEqn = do
  left  <- gets left
  right <- gets right
  return . anywhere $ \t -> do
    rule <- Index.lookup t left ++ Index.lookup t right
    let u = Rule.rhs (peel rule)
    guard (u `simplerThan` t)
    return u

rewriteFully :: Monad m => StateT Completion m Strategy
rewriteFully = do
  rules <- rewriteRules
  eqns  <- rewriteEqn
  return $ \t -> anywhere rules t ++ anywhere eqns t

normalise :: Monad m => PruningTerm -> StateT Completion m PruningTerm
normalise t = do
  rewrite <- rewriteRules
  return (normaliseWith rewrite t)

normaliseFully :: Monad m => PruningTerm -> StateT Completion m PruningTerm
normaliseFully t = do
  rewrite <- rewriteFully
  return (normaliseWith rewrite t)

newCPs :: Monad m => Label -> [Labelled Eqn] -> StateT Completion m ()
newCPs l eqns = do
  rewrite <- rewriteRules
  let normaliseEqn (l :==: r)
        | l' == r' = Nothing
        | otherwise = Just (l' :==: r')
        where
          l' = normaliseWith rewrite l
          r' = normaliseWith rewrite r
      eqns' = catMaybes (map (moveLabel . fmap normaliseEqn) eqns)
  enqueue l eqns'

newEqn :: Monad m => Eqn -> StateT Completion m ()
newEqn eqn = newCPs noLabel [unlabelled eqn]

complete :: Monad m => StateT Completion m ()
complete = do
  res <- dequeue
  case res of
    Just eq -> do
      consider eq
      complete
    Nothing -> trace "stopped" $ do
      paused <- gets paused
      rewrite <- rewriteFully
      when (or [ rewrite t /= [] || rewrite u /= [] | t :==: u <- paused ]) $ do
        modify (\s -> s { paused = [] })
        forM_ paused $ \(t :==: u) ->
          newEqn (normaliseWith rewrite t :==: normaliseWith rewrite u)
        complete

consider :: Monad m => Eqn -> StateT Completion m ()
consider (l :==: r) = do
  l <- normaliseFully l
  r <- normaliseFully r
  when (l /= r) $ do
    let eqn = l :==: r
    Completion { maxSize = maxSize, maxEqSize = maxEqSize } <- get
    case orient eqn of
      Just rule | size l <= maxSize && size r <= maxSize -> do
        l <- add (Rule rule)
        interreduce (Rule rule)
        addCriticalPairs l (Rule rule)
      Nothing | size l <= maxEqSize && size r <= maxEqSize -> do
        left1  <- gets (map peel . Index.elems . left)
        unless (or [ undirect rule `subsumes` eqn | rule <- left1 ]) $ do
          removeSubsumptions eqn
          left  <- gets (map peel . Index.elems . left)
          l <- add (Eqn eqn)
          mapM_ interreduce (direct eqn)
          mapM_ (addCriticalPairs l) (usort (map canonicalise (direct eqn)))
      _ -> modify (\s -> s { paused = eqn:paused s })

removeSubsumptions :: Monad m => Eqn -> StateT Completion m ()
removeSubsumptions eqn = do
  left <- gets (map (fmap undirect) . Index.elems . left)
  let subsumed = filter (subsumes eqn . peel) left
  (if null subsumed then id else trace ("subsumed by " ++ prettyShow eqn ++ ": " ++ prettyShow subsumed)) $
    mapM_ (delete . fmap Eqn) subsumed

subsumes :: Eqn -> Eqn -> Bool
eqn1 `subsumes` eqn2 =
  r `elem` map Rules.result (Rules.fullRewrite [rule] l)
  where
    rule = order eqn1
    Rule.Rule l r = order eqn2

addCriticalPairs :: Monad m => Label -> DirectedEqn -> StateT Completion m ()
addCriticalPairs l eqn = do
  directedEqns <- directedEqns
  newCPs l $
    [ Labelled l' cp
    | Labelled l' eqn' <- directedEqns,
      cp <- usort (criticalPairs eqn eqn' ++ criticalPairs eqn' eqn) ]

add :: Monad m => DirectedEqn -> StateT Completion m Label
add eqn = trace ("add " ++ prettyShow eqn) $ do
  l <- newLabel
  case eqn of
    Rule rule ->
      modify (\s -> s { rules = Index.insert (Labelled l rule) (rules s) })
    Eqn (t :==: u) ->
      modify (\s -> s { left = Index.insert (Labelled l (Rule.Rule t u)) (left s),
                        right = Index.insert (Labelled l (Rule.Rule u t)) (right s) })
  return l

delete :: Monad m => Labelled DirectedEqn -> StateT Completion m ()
delete (Labelled l eqn) = trace ("delete " ++ prettyShow eqn) $ do
  deleteLabel l
  case eqn of
    Rule rule ->
      modify (\s -> s { rules = Index.delete (Labelled l rule) (rules s) })
    Eqn (t :==: u) ->
      modify (\s -> s { left = Index.delete (Labelled l (Rule.Rule t u)) (left s),
                        right = Index.delete (Labelled l (Rule.Rule u t)) (right s) })

data Reduction = Simplify Rule | Reorient DirectedEqn

instance Show Reduction where
  show (Simplify eqn) = "simplify " ++ prettyShow eqn
  show (Reorient eqn) = "reorient " ++ prettyShow eqn

interreduce :: Monad m => DirectedEqn -> StateT Completion m ()
interreduce eqn = do
  eqns <- halfDirectedEqns
  let reductions = catMaybes (map (moveLabel . fmap (reduce eqn)) eqns)
  sequence_ [ trace ("simplified " ++ prettyShow eqn) $ simplify l eqn | Labelled l (Simplify eqn) <- reductions ]
  sequence_ [ trace ("reoriented 1 " ++ prettyShow eqn) $ newEqn (undirect (rule eqn)) | Reorient eqn <- map peel reductions ]
  sequence_ [ trace ("reoriented 2 " ++ prettyShow eqn) $ delete (Labelled l eqn) | Labelled l (Reorient eqn) <- reductions ]

reduce :: DirectedEqn -> DirectedEqn -> Maybe Reduction
reduce new old =
  let Rule.Rule lhs rhs = rule new in
  case old of
    Rule old
      | not (lhs `isInstanceOf` Rule.lhs old) &&
        not (null (rewrite new (Rule.lhs old))) ->
          Just (Reorient (Rule old))
      | not (null (rewrite new (Rule.rhs old))) ->
          Just (Simplify old)
    Eqn (t :==: u)
      | (oriented new || not (lhs `isInstanceOf` t)) &&
        not (null (rewrite new t)) ->
          Just (Reorient old)
      | (oriented new || not (lhs `isInstanceOf` u)) &&
        not (null (rewrite new u)) ->
          Just (Reorient old)
    _ -> Nothing

simplify :: Monad m => Label -> Rule -> StateT Completion m ()
simplify l r = do
  rhs' <- normalise (Rule.rhs r)
  let r' = r { Rule.rhs = rhs' }
  modify (\s -> s { rules = Index.insert (Labelled l r')
                              (Index.delete (Labelled l r)
                                (rules s)) })

main = do
  let rs = reverse (Index.elems (rules (execState (mapM_ newEqn eqs >> complete) initialState { maxSize = 11, maxEqSize = 5 })))
  print (length rs)
  mapM_ prettyPrint rs

newAxiom :: Monad m => PropOf PruningTerm -> StateT Completion m ()
newAxiom ([] :=>: (t :=: u)) = do
  Completion { maxSize = maxSize, sizeDelta = sizeDelta } <- get
  let newSize = size t `max` size u
  when (newSize > maxSize) $
    modify (\s -> s { maxSize = newSize + sizeDelta })
  newEqn (t :==: u)
  complete
