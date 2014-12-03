{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

newtype Var = Var Char deriving (Eq, Ord, Enum)
instance Show Var where show (Var x) = [x]

data Term =
  Term {
    constant :: Rational,
    -- Invariant: no coefficient is zero
    vars :: Map Var Rational }
  deriving (Eq, Ord)
instance Show Term where
  show (Term a vs)
    | Map.null vs = showRat a
    | a == 0 = showVars vs
    | otherwise = showRat a ++ " + " ++ showVars vs
    where
      showVars vs = intercalate " + " [ showRat a ++ show x | (x, a) <- Map.toList vs ]
showRat :: Rational -> String
showRat a
  | denominator a == 1 = show (numerator a)
  | otherwise = "(" ++ show a ++ ")"

constTerm :: Rational -> Term
constTerm a = Term a Map.empty

var :: Var -> Term
var x = Term 0 (Map.singleton x 1)

mapTerm :: (Rational -> Rational) -> Term -> Term
mapTerm f x =
  Term {
    constant = f (constant x),
    vars = fmap f (vars x) }

instance Num Term where
  fromInteger n = constTerm (fromInteger n)
  x + y =
    Term {
      constant = constant x + constant y,
      vars = Map.filter (/= 0) (Map.unionWith (+) (vars x) (vars y)) }
  negate = mapTerm negate

(^*) :: Rational -> Term -> Term
0 ^* y = constTerm 0
x ^* y = mapTerm (x*) y

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
    pvars  :: Set Var }
  deriving (Eq, Ord)

instance Show Problem where
  show Unsolvable = "Unsolvable"
  show p =
    "[" ++ intercalate ", " xs ++ "]"
    where
      xs =
        [show t ++ " >= 0" | t <- Set.toList (pos p)] ++
        [show x ++ " >= " ++ showRat a | (x, a) <- Map.toList (lower p)] ++
        [show x ++ " <= " ++ showRat a | (x, a) <- Map.toList (upper p)]

empty :: Problem
empty = Problem Set.empty Map.empty Map.empty Set.empty

problem :: [Term] -> Problem
problem ts = addTerms ts (addVars ts empty)

infix 4 ===, <==, >==
(===), (<==), (>==) :: Term -> Term -> [Term]
t <== u = [u - t]
t >== u = u <== t
t === u = (t <== u) ++ (t >== u)

addVars :: [Term] -> Problem -> Problem
addVars ts p =
  p { pvars = Set.union (Set.fromList vs) (pvars p) }
  where
    vs = concatMap (Map.keys . vars) ts

addTerms :: [Term] -> Problem -> Problem
addTerms _ Unsolvable = Unsolvable
addTerms ts p = foldr addTerm (addBounds bs p) us
  where
    (bs, us) = partition ((== 1) . Map.size . vars) ts

addTerm :: Term -> Problem -> Problem
addTerm t p
  | Map.null (vars t) =
    if constant t < 0 then Unsolvable else p
  | t `Set.member` pos p || redundant p t = p
  | otherwise =
    p { pos = Set.insert t (Set.filter (not . implies p t) (pos p)) }

addBounds :: [Term] -> Problem -> Problem
addBounds [] p = p
addBounds bs p =
  prune p { lower = Map.unionWith max (lower p) lower',
            upper = Map.unionWith min (upper p) upper' }
  where
    (lower', upper') = foldr op (Map.empty, Map.empty) bs
    op t (l, u)
      | a > 0 = (Map.insertWith max x b l, u)
      | a < 0 = (l, Map.insertWith min x b u)
      where
        (x, a) = Map.findMin (vars t)
        b = negate (constant t) / a

prune :: Problem -> Problem
prune p =
  p { pos = Set.filter (not . redundant p) (pos p) }

redundant p t =
  trivial p t ||
  or [ implies p u t && (t < u || not (implies p t u)) | u <- Set.toList (pos p), t /= u ]

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

data Step = Stop | Eliminate Var [Term] [Term] Problem deriving Show

eliminations :: Problem -> [Step]
eliminations p =
  map snd .
  sortBy (comparing fst) $
    [ eliminate x p | x <- Set.toList (pvars p) ]

eliminate :: Var -> Problem -> (Int, Step)
eliminate x p =
  -- Number of terms added by the elimination
  (length ls * length us - length ls - length us,
   case nontrivial ls && nontrivial us && any (== 0) ts of
     False ->
       Eliminate x ls us (addTerms ts p')
     True ->
       -- If we have c >= x >= c, eliminate x by doing ls >= c, c >= rs
       let (c:_) = sortBy (comparing (Map.size . vars)) (intersect ls us)
           ts = [ t - c | t <- us ] ++ [ c - u | u <- ls ] in
       Eliminate x [c] [c] (addTerms ts p'))
  where
    (ls, us, p') = focus x p
    ts = [ t - u | t <- us, u <- ls ]
    nontrivial (_:_:_) = True
    nontrivial _ = False

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

foldDelete :: Ord a => (a -> b -> Maybe b) -> b -> Set a -> (b, Set a)
foldDelete op e s = Set.foldr op' (e, s) s
  where
    op' x (y, s) =
      case op x y of
        Nothing -> (y, s)
        Just y' -> (y', Set.delete x s)

solve :: Problem -> Maybe (Map Var Rational)
solve Unsolvable = Nothing
solve p | Set.null (pos p) = Just (Map.fromList xs)
  where
    xs =
      [ (x, solveBounds (l, u))
      | x <- Set.toList (pvars p),
        let l = Map.lookup x (lower p),
        let u = Map.lookup x (upper p) ]
solve p = do
  m <- solve p'
  let a = solveBounds (try maximum (map (eval m) ls),
                       try minimum (map (eval m) us))
  return (Map.insert x a m)
  where
    Eliminate x ls us p':_ = eliminations p
    try f [] = Nothing
    try f xs = Just (f xs)

solveBounds :: (Maybe Rational, Maybe Rational) -> Rational
solveBounds (x, y) = fromMaybe 0 (x `mplus` y)

-- Debugging function
trace :: Problem -> [Step]
trace Unsolvable = []
trace p | Set.null (pos p) = []
trace p = s:trace p'
  where
    s@(Eliminate _ _ _ p'):_ = eliminations p

x = var (Var 'x')
y = var (Var 'y')
z = var (Var 'z')
w = var (Var 'w')

cs =
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

prob0 =
  problem cs

prob1 = problem ((x - y <== -1) ++ cs)
prob2 = problem ((x - y >== 1) ++ cs)
prob3 = problem ((x - y === 1) ++ cs)

prob4 =
  addTerms cs' $
  addTerms cs $
  addVars cs $
  empty
  where
    cs = concat [x + y >== 0, x + 2^*y >== 0]
    cs' = y === 0

prob5 =
  problem . concat $ [
    x - 3^*y + 2^*z + w === -4,
    2^*x - 6^*y + z + 4^*w === 1,
    -1^*x + 2^*y + 3^*z + 4^*w === 12,
    -1^*y + z + w === 0 ]

main =
 defaultMain [
   bench "prob0" (whnf solve prob0),
   bench "prob0 (full)" (whnf (solve . problem) cs),
   bench "prob1" (whnf solve prob1),
   bench "prob2" (whnf solve prob2),
   bench "prob3" (whnf solve prob3),
   bench "prob5" (whnf solve prob5)]

-- {-# NOINLINE go #-}
-- go :: (a -> b) -> a -> c -> IO ()
-- go f x _ = f x `seq` return ()

-- main =
--   forM_ [1..100000] (go (solve . problem) cs)
