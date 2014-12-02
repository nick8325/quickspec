import Data.Ratio
import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
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
  fromInteger n = constTerm (fromInteger n)
  x + y =
    Term {
      constant = constant x + constant y,
      vars = Map.filter (/= 0) (Map.unionWith (+) (vars x) (vars y)) }
  negate x =
    Term {
      constant = negate (constant x),
      vars = fmap negate (vars x) }

constTerm :: Rational -> Term
constTerm a = Term a Map.empty

(^*) :: Rational -> Term -> Term
0 ^* _ = 0
x ^* y =
  Term {
    constant = x * constant y,
    vars = fmap (x*) (vars y) }

var :: Var -> Term
var x = Term 0 (Map.singleton x 1)

eval :: Map Var Rational -> Term -> Rational
eval m t =
  constant t +
  sum [ a * Map.findWithDefault err x m | (x, a) <- Map.toList (vars t) ]
  where
    err = error "eval: variable not bound"

data Problem =
  Unsolvable |
  Problem {
    pos    :: Set Term,
    lower  :: Map Var Rational,
    upper  :: Map Var Rational,
    pvars  :: Set Var,
    solved :: [(Var, [Term], [Term])] }
  deriving (Eq, Ord, Show)

addTerm :: Term -> Problem -> Problem
addTerm _ Unsolvable = Unsolvable
addTerm t p
  | t `Set.member` pos p = p
  | redundant p t = p
addTerm t p =
  case Map.toList (vars t) of
    [] | constant t < 0 -> Unsolvable
    [(x, a)]
      | a > 0 ->
        prune p { lower = Map.insertWith max x y (lower p) }
      | a < 0 ->
        prune p { upper = Map.insertWith min x y (upper p) }
      where
        y = negate (constant t) / a
    _ ->
      p { pos = Set.insert t (Set.filter (not . implies p t) (pos p)) }

infix 4 ===, <==, >==
(===), (<==), (>==) :: Term -> Term -> [Term]
t <== u = [u - t]
t >== u = u <== t
t === u = (t <== u) ++ (t >== u)

x = var (Var 0)
y = var (Var 1)
z = var (Var 2)
w = var (Var 3)

problem :: [Term] -> Problem
problem ts = foldr addTerm (Problem Set.empty Map.empty Map.empty (Set.fromList vs) []) ts
  where
    vs = concatMap (Map.keys . vars) ts

prob0 =
  problem $
  concat [
    x >== 1,
    y >== 1,
    z >== 1,
    w >== 1,
    (-1) ^* x + 1 ^* y <== -1,
    x + y - w + 1 <== -1,
    x - z - w - 1 <== -1,
    x + y - z + w + 2 >== 0,
    y - z + w + 1 >== 0 ]

prob1 = foldr addTerm prob0 (x - y <== -1)
prob2 = foldr addTerm prob0 (x - y >== 1)

foldDelete :: Ord a => (a -> b -> Maybe b) -> b -> Set a -> (b, Set a)
foldDelete op e s = Set.foldr' op' (e, s) s
  where
    op' x (y, s) =
      case op x y of
        Nothing -> (y, s)
        Just y' -> (y', Set.delete x s)

focus :: Var -> Problem -> ([Term], [Term], Problem)
focus x p = (ls', us', p' { pos = pos' })
  where
    p' = p {
      lower = Map.delete x (lower p),
      upper = Map.delete x (upper p),
      pvars = Set.delete x (pvars p) }
    ((ls', us'), pos') = foldDelete op (ls, us) (pos p')
    (ls, us) = (bound (lower p), bound (upper p))
    bound s = maybeToList (fmap constTerm (Map.lookup x s))
    op t (ls, us) = do
      a <- Map.lookup x (vars t)
      let b = negate (recip a) ^* t { vars = Map.delete x (vars t) }
      if a > 0
        then return (b:ls, us)
        else return (ls, b:us)

implies :: Problem -> Term -> Term -> Bool
-- a1x1+...+anxn + b >= 0 ==> c1x1+...+cnxn + d >= 0
-- <=>
-- (c1-a1)x1+...+(cn-an)x2 + d - b >= 0
implies p t u = trivial p (u - t)
-- Note: if t implies u and u implies t then t is syntactically equal to u:
-- If t implies u then:
--    minValue (u - t) >= 0
-- => maxValue (t - u) <= 0
-- => minValue (t - u) <= 0
-- If u also implies t than minValue (t - u) >= 0
-- so minValue (t - u) = maxValue (t - u) = 0 so t - u = 0.

trivial :: Problem -> Term -> Bool
trivial p t =
  case minValue p t of
    Just a | a >= 0 -> True
    _ -> False

minValue :: Problem -> Term -> Maybe Rational
minValue p t = do
  as <- fmap sum (mapM varValue (Map.toList (vars t)))
  return (as + constant t)
  where
    varValue (x, a)
      | a > 0 = fmap (a *) (Map.lookup x (lower p))
      | otherwise = fmap (a *) (Map.lookup x (upper p))

reduce :: Problem -> Problem
reduce p = do
  case step p of
    Nothing -> p
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
    between (x, y) = fromMaybe 0 (x `mplus` y)
    try f [] = Nothing
    try f xs = Just (f xs)

solve :: Problem -> Maybe (Map Var Rational)
solve p =
  case reduce p of
    Unsolvable -> Nothing
    p -> Just (solution p)

step :: Problem -> Maybe Problem
step Unsolvable = Nothing
step p = listToMaybe (eliminateOne p)

prune :: Problem -> Problem
prune p =
  p { pos = Set.filter (not . redundant p) (pos p) }

redundant p t =
  trivial p t ||
  or [ implies p u t | u <- Set.toList (pos p), t /= u ]

eliminateOne :: Problem -> [Problem]
eliminateOne p =
  map snd .
  sortBy (comparing fst) $
    [ eliminate x p | x <- Set.toList (pvars p) ]

eliminate :: Var -> Problem -> (Int, Problem)
eliminate x p =
  (length ts - length ls - length us,
   foldr addTerm p' { solved = (x, ls, us):solved p' } ts)
  where
    (ls, us, p') = focus x p
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
