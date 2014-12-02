import Data.Ratio
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Monoid
import Data.Maybe
import Data.List
import Data.Ord
import Control.Monad
import Criterion.Main

data Term =
  Term {
    constant :: Rational,
    vars :: Map Var Rational }
  deriving (Eq, Ord, Show)

--data Var = Var String | New Int deriving (Eq, Ord, Show)
newtype Var = Var Int deriving (Eq, Ord, Show)

instance Num Term where
  fromInteger n = Term (fromInteger n) Map.empty
  x + y =
    Term {
      constant = constant x + constant y,
      vars = Map.filter (/= 0) (Map.unionWith (+) (vars x) (vars y)) }
  negate x =
    Term {
      constant = negate (constant x),
      vars = fmap negate (vars x) }

(^*) :: Rational -> Term -> Term
0 ^* _ = 0
x ^* y =
  Term {
    constant = x * constant y,
    vars = fmap (x*) (vars y) }

var :: Var -> Term
var x = Term 0 (Map.singleton x 1)

size :: Term -> Rational
size t = constant t + sum (Map.elems (vars t))

eval :: Map Var Rational -> Term -> Rational
eval m t =
  constant t +
  sum [ a * Map.findWithDefault err x m | (x, a) <- Map.toList (vars t) ]
  where
    err = error "eval: variable not bound"

data Problem =
  Problem {
    pos    :: Set Term,
    lower  :: Map Var Rational,
    upper  :: Map Var Rational,
    solved :: [(Var, [Term], [Term])] }
  deriving (Eq, Ord, Show)

addTerm :: Term -> Problem -> Problem
addTerm t p =
  case Map.toList (vars t) of
    [(x, a)]
      | a > 0 ->
        p { lower = Map.insertWith max x y (lower p) }
      | a < 0 ->
        p { upper = Map.insertWith min x y (upper p) }
      where
        y = negate (constant t) / a
    _ -> p { pos = Set.insert t (pos p) }

instance Monoid Problem where
  mempty = Problem Set.empty Map.empty Map.empty []
  x `mappend` y =
    Problem {
      pos    = pos x `Set.union` pos y,
      lower  = Map.unionWith max (lower x) (lower y),
      upper  = Map.unionWith min (upper x) (upper y),
      solved = solved x ++ solved y }

problemVars :: Problem -> Set Var
problemVars p =
  Set.unions [ toSet (vars t) | t <- Set.toList (pos p) ] `Set.union`
  toSet (lower p) `Set.union` toSet (upper p)
  where
    toSet = Set.fromAscList . Map.keys

infix 4 ===, <==, >==
(===), (<==), (>==) :: Term -> Term -> Problem
t <== u = addTerm (u - t) mempty
t >== u = u <== t
t === u = mconcat [t <== u, t >== u]

x = var (Var 0)
y = var (Var 1)
z = var (Var 2)
w = var (Var 3)

prob0 =
  mconcat [
    x >== 1,
    y >== 1,
    z >== 1,
    w >== 1,
    (-1) ^* x + 1 ^* y <== -1,
    x + y - w + 1 <== -1,
    x - z - w - 1 <== -1,
    x + y - z + w + 2 >== 0,
    y - z + w + 1 >== 0 ]

prob1 = prob0 `mappend` (x - y <== -1)
prob2 = prob0 `mappend` (x - y >== 1)

data View = Lower Var Term | Upper Var Term

view :: Var -> Term -> Maybe View
view x t =
  case Map.lookup x (vars t) of
    Nothing -> Nothing
    Just a | a > 0 -> Just (Lower x (negate (recip a) ^* remove x t))
    Just a | a < 0 -> Just (Upper x (negate (recip a) ^* remove x t))
  where
    remove x t = t { vars = Map.delete x (vars t) }

focus :: Var -> Problem -> ([View], Problem)
focus x p = foldr op (bs, p { lower = Map.delete x (lower p), upper = Map.delete x (upper p) }) (Set.toList (pos p))
  where
    op t (vs, p) =
      case view x t of
        Nothing -> (vs, p)
        Just v -> (v:vs, p { pos = Set.delete t (pos p) })
    bs =
      [ Lower x (Term a Map.empty) | Just a <- [Map.lookup x (lower p)] ] ++
      [ Upper x (Term a Map.empty) | Just a <- [Map.lookup x (upper p)] ]

implies :: Problem -> Term -> Term -> Bool
-- a1x1+...+anxn + b >= 0 ==> c1x1+...+cnxn + d >= 0
-- <=>
-- (c1-a1)x1+...+(cn-an)x2 + d - b >= 0
implies p t u = trivial p (u - t)

trivial :: Problem -> Term -> Bool
trivial p t =
  case minValue p t of
    Just a | a >= 0 -> True
    _ -> False

consistent :: Problem -> Term -> Bool
consistent p t =
  case maxValue p t of
    Just a | a < 0 -> False
    _ -> True

minValue, maxValue :: Problem -> Term -> Maybe Rational
minValue p t = do
  as <- fmap sum (mapM varValue (Map.toList (vars t)))
  return (as + constant t)
  where
    varValue (x, a)
      | a > 0 = fmap (a *) (Map.lookup x (lower p))
      | otherwise = fmap (a *) (Map.lookup x (upper p))

maxValue p t = fmap negate (minValue p (negate t))

reduce :: Problem -> Maybe Problem
reduce p = do
  guard (all (consistent p) (Set.toList (pos p)))
  case step p of
    Nothing -> Just p
    Just p' -> reduce p'

solution :: Problem -> Map Var Rational
solution p
  | not (Set.null (pos p)) = error "problem not solved yet"
  | otherwise = foldl' op Map.empty (solved p)
  where
    op m (x, los, his) =
      Map.insert x a m
      where
        a = between (try maximum (map (eval m) los),
                     try minimum (map (eval m) his))
    between (Just x, Just y) | x > y = error "between: inconsistent bounds"
    between (Nothing, Nothing) = 0
    between (Nothing, Just x)  = x
    between (Just x,  _)       = x
    try f [] = Nothing
    try f xs = Just (f xs)

solve :: Problem -> Maybe (Map Var Rational)
solve p = fmap solution (reduce p)

step :: Problem -> Maybe Problem
step p = listToMaybe (steps p)

steps :: Problem -> [Problem]
steps p =
  [ p  { pos = Set.delete t (pos p) } | t <- redundant p ] ++
  eliminateOne p

redundant :: Problem -> [Term]
redundant p =
  sortBy (comparing size)
    [ u
    | t <- Set.toList (pos p), u <- Set.toList (pos p), t /= u,
      implies p t u ]

eliminateOne :: Problem -> [Problem]
eliminateOne p =
  map snd .
  sortBy (comparing (length . fst)) $
    [ eliminate x p | x <- Set.toList (problemVars p) ]

eliminate :: Var -> Problem -> ([Term], Problem)
eliminate x p =
  (ts, 
   foldr addTerm p' { solved = (x, ls, us):solved p' } ts)
  where
    (vs, p') = focus x p
    ls = [ t | Lower _ t <- vs ]
    us = [ t | Upper _ t <- vs ]
    ts = filter (not . trivial p) [ t - u | t <- us, u <- ls ]

main =
  defaultMain [
    bench "prob0" (whnf solve prob0),
    bench "prob1" (whnf solve prob1),
    bench "prob2" (whnf solve prob2)]

-- {-# NOINLINE go #-}
-- go :: (a -> b) -> a -> c -> IO ()
-- go f x _ = f x `seq` return ()

-- main =
--   forM_ [1..10000] (go solve prob0)
