{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies, DeriveFunctor #-}
module QuickSpec.Pruning.Completion where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Utils
import QuickSpec.Signature(constant)
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
import QuickSpec.Pretty

-- type PruningTerm = Tm PruningConstant PruningVariable
-- data PruningConstant = Skolem PruningVariable | Plus | Times | Zero | One deriving (Show, Eq, Ord)
-- allFuns = [Plus, Times, Zero, One]
-- newtype PruningVariable = V Int deriving (Show, Eq, Ord, Numbered)
-- instance Sized PruningConstant where funSize _ = 1
-- x = Var (V 0)
-- y = Var (V 1)
-- z = Var (V 2)

plus t u = Fun (termConstant (constant "+" ((+) :: Int -> Int -> Int))) [t, u]
times t u = Fun (termConstant (constant "*" ((*) :: Int -> Int -> Int))) [t, u]
inv t = Fun (termConstant (constant "-" (negate :: Int -> Int))) [t]
zero = Fun (termConstant (constant "0" (0 :: Int))) []
one = Fun (termConstant (constant "1" (1 :: Int))) []
x = Var (PruningVariable 0)
y = Var (PruningVariable 1)
z = Var (PruningVariable 2)

termConstant con = TermConstant con (typ con) (arity (typ con))

eqs = [
  plus x y :==: plus y x,
  plus zero x :==: x,
  --plus x (plus y z) :==: plus y (plus x z),
  plus x (plus y z) :==: plus (plus x y) z,
  times x y :==: times y x,
  times zero x :==: zero,
  times one x :==: x,
  --times x (times y z) :==: times y (times x z),
  times x (times y z) :==: times (times x y) z,
  times x (plus y z) :==: plus (times x y) (times x z)]

type Eqn = EquationOf PruningTerm
type Rule = RuleOf PruningTerm
type PruningCP = CPOf PruningTerm

type T = StateT Completion
data Completion =
  Completion {
    maxSize     :: Int,
    sizeDelta   :: Int,
    nextLabel   :: Label,
    labels      :: Set Label,
    rules       :: Index (Labelled Rule),
    left        :: Index (Labelled Rule),
    right       :: Index (Labelled Rule),
    functions   :: Set PruningConstant,
    acFunctions :: Set PruningConstant,
    queue       :: MinQueue (Labelled SubQueue),
    paused      :: [Eqn] }
  deriving Show

initialState =
  Completion {
    maxSize = 0,
    sizeDelta = 1,
    nextLabel = 1,
    labels = Set.singleton 0,
    rules = Index.empty,
    left = Index.empty,
    right = Index.empty,
    functions = Set.empty,
    acFunctions = Set.empty,
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
  Completion { rules = rules, left = left, right = right, acFunctions = acFunctions } <- get
  let redundant = acRedundant acFunctions
  return $
    map (fmap Rule) (Index.elems rules) ++
    map (fmap Eqn) (filter (not . redundant . peel) (map (fmap undirect) (Index.elems left)))

acRedundant :: Set PruningConstant -> Eqn -> Bool
acRedundant acFuns =
  \eqn@(l :==: r) ->
    not (or [ subsumes eqn' eqn | eqn' <- map undirect rules ++ eqns ] ||
    not (null [ Index.lookup t ruleIdx | t <- [l, r] ]) ||
    not (null [ rule | t <- [l, r], rule <- Index.lookup t eqnIdx, Rule.rhs rule `simplerThan` Rule.lhs rule ])) &&
    normaliseAC acFuns l == normaliseAC acFuns r
  where
    stuff = map acStuff (Set.toList acFuns)
    rules = map fst stuff
    eqns  = concatMap snd stuff
    ruleIdx = foldr Index.insert Index.empty rules
    eqnIdx  = foldr Index.insert Index.empty (concat [[Rule.Rule l r, Rule.Rule r l] | l :==: r <- eqns ])

normaliseAC :: Set PruningConstant -> PruningTerm -> PruningTerm
normaliseAC acFuns (Var x) = Var x
normaliseAC acFuns (Fun f xs)
  | f `Set.member` acFuns = reassociate (map (normaliseAC acFuns) (sort (concatMap (flattenAC f) xs)))
    where
      reassociate xs = foldr1 (\x y -> Fun f [x, y]) xs
normaliseAC acFuns (Fun f xs) = Fun f (map (normaliseAC acFuns) xs)

flattenAC :: PruningConstant -> PruningTerm -> [PruningTerm]
flattenAC f (Fun g xs) | g == f = concatMap (flattenAC f) xs
flattenAC f t = [t]

acStuff :: PruningConstant -> (Rule, [Eqn])
acStuff f =
  (Rule.Rule (Fun f [Fun f [x, y], z]) (Fun f [x, Fun f [y, z]]),
   [Fun f [x, y] :==: Fun f [y, x],
    Fun f [x, Fun f [y, z]] :==: Fun f [y, Fun f [x, z]],
    Fun f [x, Fun f [y, z]] :==: Fun f [z, Fun f [y, x]],
    Fun f [x, Fun f [y, z]] :==: Fun f [y, Fun f [z, x]]])
  where
    x = Var (PruningVariable 0)
    y = Var (PruningVariable 1)
    z = Var (PruningVariable 2)

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
    (r:_) -> {- trace (prettyShow t ++ " -> " ++ prettyShow r) $ -} normaliseWith strat r

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

rewriteAc :: Monad m => StateT Completion m Strategy
rewriteAc = do
  acFunctions <- gets acFunctions
  let go s (Fun f _) | s == Just f = []
      go s (Fun f ts) | f `Set.member` acFunctions = go' f ts ++ nested (go (Just f)) (Fun f ts)
      go s (Fun f ts) = nested (go Nothing) (Fun f ts)
      go s (Var x) = []
      go' f ts = [ u | u <- usort (perms (concatMap (flattenAC f) ts)) >>= build f, u `simplerThan` Fun f ts ]
      build :: PruningConstant -> [PruningTerm] -> [PruningTerm]
      build _ [t] = [t]
      build f ts = [ Fun f [u, v] | (us, vs) <- splits ts, not (null us), not (null vs), u <- build f us, v <- build f vs ]
      splits :: [a] -> [([a], [a])]
      splits [] = [([], [])]
      splits (t:ts) = do
        (us, vs) <- splits ts
        [(t:us,vs), (us,t:vs)]
      perms :: [a] -> [[a]]
      perms [] = [[]]
      perms (x:xs) = perms xs >>= ins x
      ins :: a -> [a] -> [[a]]
      ins x [] = [[x]]
      ins x (y:ys) = (x:y:ys):map (y:) (ins x ys)
  return (go Nothing)

rewriteFully :: Monad m => StateT Completion m Strategy
rewriteFully = do
  rules <- rewriteRules
  eqns  <- rewriteEqn
  ac    <- rewriteAc
  return $ \t -> anywhere rules t ++ anywhere eqns t -- ++ ac t

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
      rewrite <- rewriteFully
      paused <- gets paused
      when (or [ rewrite t /= [] || rewrite u /= [] | t :==: u <- paused ]) unpause

unpause :: Monad m => StateT Completion m ()
unpause = trace "unpausing" $ do
  discoverAC
  paused <- gets paused
  rewrite <- rewriteFully
  modify (\s -> s { paused = [] })
  forM_ paused $ \(t :==: u) ->
    newEqn (normaliseWith rewrite t :==: normaliseWith rewrite u)
  complete

consider :: Monad m => Eqn -> StateT Completion m ()
consider (l :==: r) = do
  acFunctions <- gets acFunctions
  l <- normaliseFully l
  r <- normaliseFully r
  when (l /= r && not (acRedundant acFunctions (l :==: r))) $ do
    let eqn = l :==: r
    Completion { maxSize = maxSize } <- get
    case orient eqn of
      Just rule | size l <= maxSize && size r <= maxSize -> do
        l <- add (Rule rule)
        interreduce (Rule rule)
        discoverAC
        addCriticalPairs l (Rule rule)
      Nothing | size l <= maxSize && size r <= maxSize -> do
        left1  <- gets (map peel . Index.elems . left)
        unless (or [ undirect rule `subsumes` eqn | rule <- left1 ]) $ do
          removeSubsumptions eqn
          left  <- gets (map peel . Index.elems . left)
          l <- add (Eqn eqn)
          mapM_ interreduce (direct eqn)
          discoverAC
          mapM_ (addCriticalPairs l) (usort (map canonicalise (direct eqn)))
      _ -> modify (\s -> s { paused = eqn:paused s })

discoverAC :: Monad m => StateT Completion m ()
discoverAC = do
  Completion { functions = functions, acFunctions = acFunctions } <- get
  rewrite <- rewriteFully
  let newAC = filter (isAC rewrite) (Set.toList (functions Set.\\ acFunctions))
  unless (null newAC) $ trace ("Discovered AC functions " ++ prettyShow newAC) (return ())
  modify (\s -> s { acFunctions = acFunctions `Set.union` Set.fromList newAC })

isAC :: Strategy -> PruningConstant -> Bool
isAC strat con =
  normaliseWith strat l1 == normaliseWith strat r1 &&
  normaliseWith strat l2 == normaliseWith strat r2
  where
    x = Fun (skolemVariable 0) []
    y = Fun (skolemVariable 1) []
    z = Fun (skolemVariable 2) []
    l1 = Fun con [x, y]
    r1 = Fun con [y, x]
    l2 = Fun con [x, Fun con [y, z]]
    r2 = Fun con [Fun con [x, y], z]
    skolemVariable n = SkolemVariable (Variable n (typeOf ()))

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
  Completion { acFunctions = acFunctions } <- get
  case eqn of
    Eqn eqn | acRedundant acFunctions eqn -> return ()
    _ -> do
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
  sequence_ [ trace ("reoriented " ++ prettyShow eqn) $ newEqn (undirect (rule eqn)) | Reorient eqn <- map peel reductions ]
  sequence_ [ delete (Labelled l eqn) | Labelled l (Reorient eqn) <- reductions ]

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
 let s = execState (mapM_ newEqn eqs >> complete) initialState { maxSize = 9, functions = Set.fromList (funs eqs) }
 mapM_ prettyPrint (Index.elems (rules s))
 putStrLn "Equations:"
 mapM_ prettyPrint (Index.elems (left s))

seenTerm :: Monad m => PruningTerm -> StateT Completion m ()
seenTerm t = do
  modify (\s -> s { functions = Set.union (Set.fromList (funs t)) (functions s) })
  Completion { maxSize = maxSize, sizeDelta = sizeDelta } <- get
  when (size t > maxSize) $ do
    modify (\s -> s { maxSize = size t + sizeDelta })
    unpause

newAxiom :: Monad m => PropOf PruningTerm -> StateT Completion m ()
newAxiom ([] :=>: (t :=: u)) = do
  seenTerm t
  seenTerm u
  newEqn (t :==: u)
  complete

findRep :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT Completion m (Maybe PruningTerm)
findRep axioms t = do
  seenTerm t
  sequence_ [ do { seenTerm t; seenTerm u } | [] :=>: (t :=: u) <- axioms ]
  locally $ do
    sequence_ [ newEqn (t :==: u) | [] :=>: (t :=: u) <- axioms ]
    u <- normaliseFully t
    if t == u then return Nothing else return (Just u)

locally :: Monad m => StateT s m a -> StateT s m a
locally m = do
  s <- get
  x <- m
  put s
  return x

instance Pruner Completion where
  emptyPruner = initialState
  untypedRep = findRep
  untypedAxiom = newAxiom
