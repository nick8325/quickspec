{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
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
import Control.Applicative hiding (empty)

data Term a =
  Term {
    constant :: Rational,
    -- Invariant: no coefficient is zero
    vars :: Map a Rational }
  deriving (Eq, Ord)
instance Show a => Show (Term a) where
  show (Term a vs)
    | Map.null vs = showRat a
    | a == 0 = showVars vs
    | otherwise = showRat a ++ " + " ++ showVars vs
    where
      showVars vs = intercalate " + " [ showRat a ++ "*" ++ show x | (x, a) <- Map.toList vs ]
showRat :: Rational -> String
showRat a
  | denominator a == 1 = show (numerator a)
  | otherwise = "(" ++ show a ++ ")"

constTerm :: Rational -> Term a
constTerm a = Term a Map.empty

var :: a -> Term a
var x = Term 0 (Map.singleton x 1)

mapTerm :: (Rational -> Rational) -> Term a -> Term a
mapTerm f x =
  Term {
    constant = f (constant x),
    vars = fmap f (vars x) }

instance Ord a => Num (Term a) where
  fromInteger n = constTerm (fromInteger n)
  x + y =
    Term {
      constant = constant x + constant y,
      vars = Map.filter (/= 0) (Map.unionWith (+) (vars x) (vars y)) }
  negate = mapTerm negate

(^*) :: Rational -> Term a -> Term a
0 ^* y = constTerm 0
x ^* y = mapTerm (x*) y

eval :: Ord a => Map a Rational -> Term a -> Rational
eval m t =
  constant t +
  sum [ a * Map.findWithDefault err x m | (x, a) <- Map.toList (vars t) ]
  where
    err = error "eval: variable not bound"

data Bound a =
  Closed { bound :: a }
  | Open { bound :: a }
  deriving (Eq, Ord, Functor)

instance Applicative Bound where
  pure = return
  (<*>) = liftM2 ($)

instance Monad Bound where
  return = Closed
  Closed x >>= f = f x
  Open   x >>= f = Open (bound (f x))

instance Show a => Show (Bound a) where
  show (Closed x) = show x ++ " >= 0"
  show (Open x) = show x ++ " > 0"

boundTrue :: (Ord a, Num a) => Bound a -> Bool
boundTrue (Closed x) = x >= 0
boundTrue (Open x) = x > 0

data Problem a =
  Unsolvable |
  Problem {
    pos    :: Set (Bound (Term a)),
    lower  :: Map a (Bound Rational),
    upper  :: Map a (Bound Rational),
    pvars  :: Set a }
  deriving (Eq, Ord)

instance Show a => Show (Problem a) where
  show Unsolvable = "Unsolvable"
  show p =
    "[" ++ intercalate ", " xs ++ "]"
    where
      xs =
        [show t | t <- Set.toList (pos p)] ++
        [show x ++ " >= " ++ showRat a | (x, Closed a) <- Map.toList (lower p)] ++
        [show x ++ " > "  ++ showRat a | (x, Open a)   <- Map.toList (lower p)] ++
        [show x ++ " <= " ++ showRat a | (x, Closed a) <- Map.toList (upper p)] ++
        [show x ++ " < "  ++ showRat a | (x, Open a)   <- Map.toList (upper p)]

problem :: Ord a => [Bound (Term a)] -> Problem a
problem ts = addTerms ts empty

empty :: Problem a
empty = Problem Set.empty Map.empty Map.empty Set.empty

infix 4 ===, <==, >==, </=, >/=
(===), (<==), (>==), (</=), (>/=) :: Ord a => Term a -> Term a -> [Bound (Term a)]
t <== u = [Closed (u - t)]
t >== u = u <== t
t </= u = [Open (u - t)]
t >/= u = u </= t
t === u = (t <== u) ++ (t >== u)

addTerms :: Ord a => [Bound (Term a)] -> Problem a -> Problem a
addTerms _ Unsolvable = Unsolvable
addTerms ts p =
  addDerivedTerms ts p { pvars = Set.union vs (pvars p) }
  where
    vs = Set.unions (map (Set.fromAscList . Map.keys . vars . bound) ts)

addDerivedTerms :: Ord a => [Bound (Term a)] -> Problem a -> Problem a
addDerivedTerms _ Unsolvable = Unsolvable
addDerivedTerms ts p = foldr addTerm (addBounds bs p) us
  where
    (bs, us) = partition ((== 1) . Map.size . vars . bound) ts

addTerm :: Ord a => Bound (Term a) -> Problem a -> Problem a
addTerm _ Unsolvable = Unsolvable
addTerm t p
  | Map.null (vars (bound t)) =
    if boundTrue (fmap constant t) then p else Unsolvable
  | t `Set.member` pos p || redundant p t = p
  | otherwise =
    p { pos = Set.insert t (Set.filter (not . implies p t) (pos p)) }

addBounds :: Ord a => [Bound (Term a)] -> Problem a -> Problem a
addBounds [] p = p
addBounds bs p =
  prune p { lower = Map.unionWith bmax (lower p) lower',
            upper = Map.unionWith bmin (upper p) upper' }
  where
    (lower', upper') = foldr op (Map.empty, Map.empty) bs
    op t (l, u)
      | a > 0 = (Map.insertWith bmax x b l, u)
      | a < 0 = (l, Map.insertWith bmin x b u)
      where
        (x, a) = Map.findMin (vars (bound t))
        b = fmap (\t -> negate (constant t) / a) t
    bmax x y
      | bound x > bound y = x
      | bound y > bound x = y
      | otherwise = liftM2 const x y
    bmin x y = fmap negate (bmax (fmap negate x) (fmap negate y))

prune :: Ord a => Problem a -> Problem a
prune p =
  p { pos = Set.filter (not . redundant p) (pos p) }

redundant p t =
  trivial p t ||
  or [ implies p u t && (t < u || not (implies p t u)) | u <- Set.toList (pos p), t /= u ]

implies :: Ord a => Problem a -> Bound (Term a) -> Bound (Term a) -> Bool
-- a1x1+...+anxn + b >= 0 ==> c1x1+...+cnxn + d >= 0
-- <=>
-- (c1-a1)x1+...+(cn-an)x2 + d - b >= 0
implies p t u = trivial p (b t u (bound u - bound t))
  where
    b Closed{} Open{} = Open
    b _        _      = Closed

trivial :: Ord a => Problem a -> Bound (Term a) -> Bool
trivial p t =
  case minValue p (bound t) of
   Just a -> check a t
   _ -> False
  where
    check (Closed x) Open{} = x > 0
    check x _ = bound x >= 0

minValue :: Ord a => Problem a -> Term a -> Maybe (Bound Rational)
minValue p t = do
  as <- mapM varValue (Map.toList (vars t))
  return (fmap (constant t +) (fmap sum (sequence as)))
  where
    varValue (x, a) =
      fmap (fmap (a*))
        (Map.lookup x (if a > 0 then lower p else upper p))

data Step a = Stop | Eliminate a [Bound (Term a)] [Bound (Term a)] (Problem a) deriving Show

eliminations :: Ord a => Problem a -> [Step a]
eliminations p =
  map snd .
  sortBy (comparing fst) $
    [ eliminate x p | x <- Set.toList (pvars p) ]

eliminate :: Ord a => a -> Problem a -> (Int, Step a)
eliminate x p =
  -- Number of terms added by the elimination
  (length ls * length us - length ls - length us,
   -- If we have c >= x >= c, eliminate x by doing ls >= c, c >= rs,
   -- otherwise generate ls >= rs
   case nontrivial ls && nontrivial us && any ((== 0) . bound) ts of
     False ->
       Eliminate x ls us (addDerivedTerms ts p')
     True ->
       case sortBy (comparing (Map.size . vars . bound)) (intersect ls us) of
        Closed c:_ ->
          let ts = [fmap (subtract c) t | t <- us] ++ [fmap (c -) u | u <- ls] in
          Eliminate x [Closed c] [Closed c] (addDerivedTerms ts p')
        _ ->
          -- c > x > c or similar
          Eliminate x ls us Unsolvable)
  where
    (ls, us, p') = focus x p
    ts = [ liftM2 (-) t u | t <- us, u <- ls ]
    nontrivial (_:_:_) = True
    nontrivial _ = False

focus :: Ord a => a -> Problem a -> ([Bound (Term a)], [Bound (Term a)], Problem a)
focus x p = (ls', us', p' { pos = pos' })
  where
    p' = p {
      lower = Map.delete x (lower p),
      upper = Map.delete x (upper p),
      pvars = Set.delete x (pvars p) }
    ((ls', us'), pos') = foldDelete op (ls, us) (pos p')
    (ls, us) = (boundFor (lower p), boundFor (upper p))
    boundFor s = maybeToList (fmap (fmap constTerm) (Map.lookup x s))
    op t (ls, us) = do
      let vs = vars (bound t)
      a <- Map.lookup x vs
      let b = negate (recip a) ^* (bound t) { vars = Map.delete x vs }
      if a > 0
        then return (t { bound = b }:ls, us)
        else return (ls, t { bound = b }:us)

foldDelete :: Ord a => (a -> b -> Maybe b) -> b -> Set a -> (b, Set a)
foldDelete op e s = Set.foldr op' (e, s) s
  where
    op' x (y, s) =
      case op x y of
        Nothing -> (y, s)
        Just y' -> (y', Set.delete x s)

solve :: Ord a => Problem a -> Maybe (Map a Rational)
solve Unsolvable = Nothing
solve p | Set.null (pos p) =
  fmap Map.fromList $
    forM (Set.toList (pvars p)) $ \x -> do
      let l = Map.lookup x (lower p)
          u = Map.lookup x (upper p)
      a <- solveBounds (l, u)
      return (x, a)
solve p = do
  m <- solve p'
  let Just a = solveBounds (try maximum (map (fmap (eval m)) ls),
                            try minimum (map (fmap (eval m)) us))
  return (Map.insert x a m)
  where
    Eliminate x ls us p':_ = eliminations p
    try f [] = Nothing
    try f xs = Just (f xs)

solveBounds :: (Maybe (Bound Rational), Maybe (Bound Rational)) -> Maybe Rational
solveBounds (Just x, Just y)
  | empty x y = Nothing
    -- Try to give an integer solution if possible.
  | boundTrue (fmap (subtract a) y) = Just a
  | otherwise = Just ((bound x+bound y)/2)
  where
    empty (Closed x) (Closed y) = x > y
    empty x y = bound x >= bound y
    a = fromInteger (floor (bound x+1))
solveBounds (x, y) =
  fmap solveBound x `mplus`
  fmap (negate . solveBound . fmap negate) y `mplus`
  return 0
  where
    solveBound (Closed x) = x
    solveBound (Open x) = fromInteger (floor (x+1))

-- Debugging function
trace :: Ord a => Problem a -> [Step a]
trace Unsolvable = []
trace p | Set.null (pos p) = []
trace p = s:trace p'
  where
    s@(Eliminate _ _ _ p'):_ = eliminations p

x = var 'x'
y = var 'y'
z = var 'z'
w = var 'w'

cs0 =
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
cs1 = cs0 ++ (x - y <== -1)
cs2 = cs0 ++ (x - y >== 1)
cs3 = cs0 ++ (x - y === 1)

prob0 = problem cs0
prob1 = problem cs1
prob2 = problem cs2
prob3 = problem cs3

prob4 =
  addTerms cs' $
  addTerms cs $
  empty
  where
    cs = concat [x + y >== 0, x + 2^*y >== 0]
    cs' = y === 0

cs5 =
  concat $ [
    x - 3^*y + 2^*z + w === -4,
    2^*x - 6^*y + z + 4^*w === 1,
    -1^*x + 2^*y + 3^*z + 4^*w === 12,
    -1^*y + z + w === 0 ]

prob5 = problem cs5

-- Should be unsatisfiable
prob6 =
  problem . concat $ [
    -1 + x - y - z >== 0,
    y >== 1,
    z >== 1,
    x <== 2 ]

prob7 =
  problem . concat $ [
    1 <== x + y,
    2 <== 0 ]

main =
 defaultMain [
   bench "prob0" (whnf solve prob0),
   bench "prob1" (whnf solve prob1),
   bench "prob2" (whnf solve prob2),
   bench "prob3" (whnf solve prob3),
   bench "prob5" (whnf solve prob5),
   bench "cs0" (whnf (solve . problem) cs0),
   bench "cs1" (whnf (solve . problem) cs1),
   bench "cs2" (whnf (solve . problem) cs2),
   bench "cs3" (whnf (solve . problem) cs3),
   bench "cs5" (whnf (solve . problem) cs5)]

-- {-# NOINLINE go #-}
-- go :: (a -> b) -> a -> c -> IO ()
-- go f x _ = f x `seq` return ()

-- main =
--   forM_ [1..100000] (go (solve . problem) cs)
