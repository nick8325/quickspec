{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances, TypeOperators, ScopedTypeVariables, FlexibleContexts #-}
import Prelude hiding ((/))
import qualified Prelude
import Data.Ratio
import Control.Monad
import Control.Monad.IO.Class
import Test.QuickCheck hiding (Result, shuffle)
import Test.QuickCheck.Gen hiding (shuffle)
import Test.QuickCheck.Random
import Data.Ord
import Data.Monoid
import Data.List hiding ((\\))
import qualified Data.List
import QuickSpec hiding (compose, (\\), Result, apply, simplify)
import qualified QuickSpec as QS
import Data.Maybe
import qualified Data.Map as Map

class Fractional a => Conj a where
  conj :: a -> a
  norm :: a -> Rational
  it :: Gen a

instance Conj Rational where
  conj x = x
  norm x = x*x
  it = liftM2 (Prelude./) (elements [-10..10]) (elements [1..10])

instance Conj a => Conj (a, a) where
  conj (x, y) = (conj x, negate y)
  norm (x, y) = norm x + norm y
  it = liftM2 (,) it it

instance Conj a => Num (a, a) where
  fromInteger n = (fromInteger n, 0)
  (x, y) + (z, w) = (x + z, y + w)
  (a, b) * (c, d) = (a * c - conj d * b, d * a + b * conj c)
  negate (x, y) = (negate x, negate y)

instance Conj a => Fractional (a, a) where
  fromRational x = (fromRational x, 0)
  recip x = conj x * fromRational (recip (norm x))

newtype Complex = Complex (Rational, Rational) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)
newtype Quaternion = Quaternion (Complex, Complex) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)
newtype Octonion = Octonion (Quaternion, Quaternion) deriving (Eq, Ord, Num, Typeable, Fractional, Conj, Arbitrary, CoArbitrary, Show)

class Group a where
  ident :: a
  op    :: a -> a -> a
  inv   :: a -> a

instance (Group a, Group b) => Group (a, b) where
  ident = (ident, ident)
  op (x, y) (x', y') = (op x x', op y y')
  inv (x, y) = (inv x, inv y)

instance Group Octonion where
  ident = 1
  op    = (*)
  inv   = recip

newtype Perm = Perm { unPerm :: [Int] } deriving (Eq, Ord, Show, CoArbitrary)
newtype Perms = Perms { unPerms :: [Perm] } deriving (Eq, Ord, Show, CoArbitrary)

instance Arbitrary Perms where
  arbitrary =
    fmap Perms $
      mapM (fmap Perm . shuffle . unPerm) (unPerms ident)

instance Group Perms where
  ident = Perms $ map idPerm [0..10]
  op (Perms xs) (Perms ys) = Perms (zipWith opPerm xs ys)
  inv (Perms xs) = Perms (map invPerm xs)

idPerm :: Int -> Perm
idPerm n = Perm [0..n-1]

opPerm :: Perm -> Perm -> Perm
opPerm (Perm xs) (Perm ys) = Perm [ ys !! x | x <- xs ]

invPerm :: Perm -> Perm
invPerm (Perm xs) =
  Perm . map snd . sort $ zip xs [0..]

shuffle :: forall a. (Ord a, CoArbitrary a) => [a] -> Gen [a]
shuffle xs = do
  f <- resize 100 arbitrary :: Gen (a -> Large Int)
  return (sortBy (comparing f) xs)

data Ext a = Norm a | Weird a deriving (Eq, Ord, Typeable, Show)

instance Arbitrary a => Arbitrary (Ext a) where
  arbitrary = oneof [fmap Norm arbitrary, fmap Weird arbitrary]
instance CoArbitrary a => CoArbitrary (Ext a) where
  coarbitrary (Norm x) = variant (0 :: Int) . coarbitrary x
  coarbitrary (Weird x)  = variant (1 :: Int) . coarbitrary x
instance Group a => Group (Ext a) where
  ident = Norm ident
  inv (Norm x) = Norm (inv x)
  inv (Weird x)  = Weird  x
  op (Norm x) (Norm y) = Norm (op x y)
  op (Weird x)  (Norm y) = Weird (op x (inv y))
  op (Norm x) (Weird y)  = Weird (op y x)
  op (Weird x)  (Weird y)  = Norm (op (inv y) x)

data Three = T0 | T1 | T2 deriving (Eq, Ord, Typeable, Show, Enum)

instance Arbitrary Three where
  arbitrary = elements [T0, T1, T2]

instance CoArbitrary Three where
  coarbitrary = variant . fromEnum

instance Group Three where
  ident = T0
  op x y = toEnum ((fromEnum x + fromEnum y) `mod` 3)
  inv T0 = T0
  inv T1 = T2
  inv T2 = T1

newtype ThreeFour = TF (Three, Three, Three, Three) deriving (Eq, Ord, Typeable, Show, Arbitrary, CoArbitrary)

instance Group ThreeFour where
  ident = TF (T0, T0, T0, T0)
  op (TF (x1, x2, x3, x4)) (TF (y1, y2, y3, y4)) = TF (z1, z2, z3, z4)
    where
      z1 = x1 `op` y1
      z2 = x2 `op` y2
      z3 = x3 `op` y3
      z4 = (x4 `op` y4) `op` toEnum (((fromEnum x3 - fromEnum y3) * (fromEnum x1 * fromEnum y2 - fromEnum x2 * fromEnum y1)) `mod` 3)
  inv x@(TF (x1, x2, x3, x4)) = y
    where
      [y] = [y | y <- cands, x `op` y == ident]
      cands = [TF (inv x1, inv x2, inv x3, y4) | y4 <- [T0, T1, T2]]

newtype It = It Cayley {-(Octonion, Ext Perms)-} deriving (Eq, Ord, Typeable, CoArbitrary, Group, Show)
instance Arbitrary It where arbitrary = fmap It arbitrary
--instance Arbitrary It where arbitrary = liftM2 (curry It) it arbitrary

(\\), (/) :: It -> It -> It
a / b = a `op` inv b
b \\ a = inv b `op` a

type ItFun = Fun It
newtype Fun a = ItFun [PrimFun a] deriving (Typeable, Arbitrary)
data PrimFun a = L a | R a | Invert
instance Arbitrary a => Arbitrary (PrimFun a) where
  arbitrary = oneof [fmap L arbitrary, fmap R arbitrary, return Invert]

apply :: Group a => Fun a -> a -> a
apply (ItFun xs) = foldr (.) id (map apply1 xs)
  where
    apply1 (L x) y = x `op` y
    apply1 (R x) y = y `op` x
    apply1 Invert x = inv x

instance Group a => Group (Fun a) where
  ident = ItFun []
  op (ItFun xs) (ItFun ys) = ItFun (xs++ys)
  inv (ItFun xs) = ItFun (map inv1 (reverse xs))
    where
      inv1 (L x) = L (inv x)
      inv1 (R x) = R (inv x)
      inv1 Invert = Invert

l x = ItFun [L x]
r x = ItFun [R x]
j   = ItFun [Invert]
t x = r x `op` inv (l x)
l2 x y = l x `op` l y `op` inv (l (y `op` x))
r2 x y = r x `op` r y `op` inv (r (x `op` y))
c x y = r x `op` l y `op` r (inv x) `op` l (inv y)
jconj f = j `op` f `op` j

obsItFun :: ItFun -> Gen It
obsItFun f = fmap (apply f) arbitrary

data Const =
  -- Base constants
  One | Star | Inverse | LeftInv | RightInv |
  -- Functionals
  Id | Compose | Inversion | L1 | R1 | L2 | R2 | Apply | C | T | J | ConjJ
  deriving (Enum, Bounded, Show)
instance Pretty Const where
  pretty = text . prettyShow

instance ConLike Const where
  toConstant One       = (constant "1"    (ident :: It)) { conIndex = 1 }
  toConstant Star      = (constant "*"    (op :: It -> It -> It)) { conIndex = 2 }
  toConstant Inverse   = (constant "^-1"  (inv :: It -> It)) { conStyle = Postfix, conIndex = 3 }
  toConstant LeftInv   = (constant "\\"   ((\\) :: It -> It -> It)) { conIndex = 4 }
  toConstant RightInv  = (constant "/"    ((/) :: It -> It -> It)) { conIndex = 5 }
  toConstant Id        = (constant "id"   (ident :: ItFun)) { conIndex = 6 }
  toConstant Compose   = (constant "."    (op    :: ItFun -> ItFun -> ItFun)) { conIndex = 7 }
  toConstant Inversion = (constant "^^-1" (inv   :: ItFun -> ItFun)) { conStyle = Postfix, conIndex = 8 }
  toConstant L1        = (constant "L"   (l :: It -> ItFun))     { conStyle = Uncurried, conIndex = 9 }
  toConstant R1        = (constant "R"   (r :: It -> ItFun))     { conStyle = Uncurried, conIndex = 10 }
  toConstant L2        = (constant "L"   (l2 :: It -> It -> ItFun))    { conStyle = Uncurried, conIndex = 11 }
  toConstant R2        = (constant "R"   (r2 :: It -> It -> ItFun))    { conStyle = Uncurried, conIndex = 12 }
  toConstant Apply     = (constant "@"    (flip apply :: It -> ItFun -> It)) { conIndex = 13 }
  toConstant C         = (constant "C"    (c :: It -> It -> ItFun))     { conStyle = Uncurried, conIndex = 14 }
  toConstant T         = (constant "T"    (t :: It -> ItFun))     { conStyle = Uncurried, conIndex = 15 }
  toConstant J         = (constant "J"    (j :: ItFun)) { conIndex = 16 }
  toConstant ConjJ     = (constant "^J"   (jconj :: ItFun -> ItFun)) { conStyle = Postfix, conIndex = 17 }

sig1 =
  signature {
    constants = cs,
    maxTermSize = Just 7,
    maxTests = Just 10,
    -- QuickSpec.simplify = Just Main.simplify,
    extraPruner = Just (Waldmeister 5),
    background = [],-- quasimoufang cs,
    --background = diassociativity cs ++ loop cs,
    instances = [
      baseType (undefined :: It) ]}
  where
    cs = map toConstant [Star, Inverse, One] -- ++ [bi]
--    bi = constant "bi" (undefined :: It -> It -> It -> Bool)

diassociativity :: [Constant] -> [Prop]
diassociativity cs = map (parseProp cs) background
  where
    background = [
      "bi(X, Y, X)",
      "bi(X, Y, Y)",
      "bi(X, Y, A) & bi(X, Y, B) => bi(X, Y, *(A, B))",
      "bi(X, Y, A) & bi(X, Y, B) & bi(X, Y, C) => *(A, *(B, C)) = *(*(A, B), C)"]

loop :: [Constant] -> [Prop]
loop cs = map (parseProp cs) background
  where
    background = [
      "*(1, X) = X",
      "*(X, 1) = X",
      "*(X, ^-1(X)) = 1",
      "*(^-1(X), X) = 1"
      ]

quasimoufang :: [Constant] -> [Prop]
quasimoufang cs = map (parseProp cs) background
  where
    background = [
      "*(X, \\(X, Y)) = Y",
      "\\(X, *(X, Y)) = Y",
      "*(/(X, Y), Y) = X",
      "/(*(X, Y), Y) = X",
      "*(A,*(B,*(A,C))) = *(*(*(A,B),A),C)"
      ]

dialoop :: [Constant] -> [Prop]
dialoop cs = map (parseProp cs) background
  where
    background = [
      "*(X, *(^-1(X), Y)) = Y",
      "*(^-1(X), *(X, Y)) = Y",
      "*(*(X, ^-1(Y)), Y) = X",
      "*(*(X, Y), ^-1(Y)) = X",
      "*(X, 1) = X",
      "*(1, X) = X",
      "*(^-1(*(A,B)),*(A,*(B,*(C,D)))) = *(*(^-1(*(A,B)),*(A,*(B,C))),*(^-1(*(A,B)),*(A,*(B,D))))",
      "*(*(*(*(A,B),C),D),^-1(*(C,D))) = *(*(*(*(A,C),D),^-1(*(C,D))),*(*(*(B,C),D),^-1(*(C,D))))",
      "*(^-1(A),*(*(B,C),A)) = *(*(^-1(A),*(B,A)),*(^-1(A),*(C,A)))"
      ]

comp :: [Constant] -> [Prop]
comp cs = map (parseProp cs) background
  where
    background = [
      ".(X, .(Y, Z)) = .(.(X, Y), Z)",
      ".(id, X) = X",
      ".(X, id) = X",
      ".(X, ^^-1(X)) = id",
      "^^-1(.(X, Y)) = .(^^-1(Y), ^^-1(X))",
      "^^-1(^^-1(X)) = X"
      ]

sig2 =
  signature {
    maxTests = Just 5,
    constants = map toConstant [Id, Compose, Inversion],
    instances = [
      names (NamesFor ["f", "g", "h"] :: NamesFor ItFun),
      inst (Sub Dict :: () :- Arbitrary ItFun),
      makeInstance (\() -> observe obsItFun) ]}

sig3 =
  signature {
    constants = map toConstant [T, L1, R1], --[L1, R1, L2, R2, Apply, C, T, J, ConjJ],
    maxTests = Just 5}
    --instances = [baseType (undefined :: Result)],
    --background = background,

class (Enum a, Bounded a) => ConLike a where
  toConstant :: a -> Constant

fromConstant :: ConLike a => Signature -> Constant -> a
fromConstant sig c =
  head [ x | x <- [minBound..maxBound], toConstant x == c ]

simplify :: Signature -> Prop -> Prop
simplify sig ([] :=>: t :=: u) | typ t == typeOf (undefined :: ItFun) =
  [] :=>:
    toTerm (simplifyTerm (Fun Apply [Var v, fromTerm t])) :=:
    toTerm (simplifyTerm (Fun Apply [Var v, fromTerm u]))
  where
    v = Variable (n+1) (typeOf (undefined :: It))
    n = 1+maximum (0:map varNumber (vars t ++ vars u))
    toTerm (Fun f ts) = foldl QS.apply (Fun (toConstant f) []) (map toTerm ts)
    toTerm (Var x) = Var x
    fromTerm = mapTerm (fromConstant sig . (\c -> c { conArity = 0 })) id
simplify sig ([] :=>: t :=: u) =
  [] :=>: toTerm (simplifyTerm (fromTerm t)) :=: toTerm (simplifyTerm (fromTerm u))
  where
    toTerm (Fun f ts) = foldl QS.apply (Fun (toConstant f) []) (map toTerm ts)
    toTerm (Var x) = Var x
    fromTerm = mapTerm (fromConstant sig . (\c -> c { conArity = 0 })) id
simplify sig prop = prop

simplifyTerm :: Tm Const Variable -> Tm Const Variable
simplifyTerm (Fun Apply [x, t]) | groundFuns t = simplifyTerm (apply (toFun t) x)
{-simplifyTerm (Fun Apply [x, Fun Inversion [t]]) = simplifyTerm (Fun Inverse [Fun Apply [x, t]])
simplifyTerm (Fun Apply [x, Fun ConjJ [t]]) = simplifyTerm (Fun Inverse [Fun Apply [Fun Inverse [x], t]])
simplifyTerm (Fun Apply [x, Fun Compose [t, u]]) = simplifyTerm (Fun Apply [Fun Apply [x, u], t])-}
simplifyTerm (Fun f ts) = Fun f (map simplifyTerm ts)
simplifyTerm x = x

groundFuns t = null [ x | x <- vars t, typ x == typeOf (undefined :: ItFun) ]

toFun :: Tm Const Variable -> Fun (Tm Const Variable)
toFun (Fun Id []) = ident
toFun (Fun Compose [f, g]) = toFun f `op` toFun g
toFun (Fun Inversion [f]) = inv (toFun f)
toFun (Fun L1 [x]) = l x
toFun (Fun R1 [x]) = r x
toFun (Fun L2 [x, y]) = l2 x y
toFun (Fun R2 [x, y]) = r2 x y
toFun (Fun C [x, y]) = c x y
toFun (Fun T [x]) = t x
toFun (Fun J []) = j
toFun (Fun ConjJ [f]) = jconj (toFun f)
toFun t = error $ show t

instance Group (Tm Const Variable) where
  ident = Fun One []
  op x y = Fun Star [x, y]
  inv x = Fun Inverse [x]

{-main = do
  thy1 <- quickSpec sig1
  thy2 <- quickSpec sig2
  let sig = thy1 `mappend` thy2 `mappend` sig3
  quickSpec sig-}

explore :: [Prop] -> Signature -> IO ([Prop], Signature)
explore bg sig = do
{-main = do
  let sig = renumber --(sig1 `mappend` sig2 `mappend` sig3)
      bg = quasimoufang (constants sig)
      goal = parseProp (constants sig) "*(X, /(Y, Y)) = X"-}
  thy <- quickSpec sig
  props <- upTo (\n props -> establish n sig simps bg props) timeout (background thy Data.List.\\ background sig)
  {-putStrLn "\nShrinking..."
  props' <- shrinkProof sig bg props
  putStrLn "\nFinal chain of lemmas:"
  mapM_ prettyPrint props'-}
  return (props, sig { background = background sig ++ props })
{-
  case goal `elem` props of
    False ->
      putStrLn "Failed to prove goal"
    True -> do
      putStrLn "Proved goal!\n"
      props' <- shrinkProof sig bg props -- (props ++ [goal])-}

simps = [highord, \sig prop -> Just (simplify sig prop)]
  where
    highord _ prop
      | isHigher prop = Just prop
      | otherwise = Nothing
    isHigher ([] :=>: t :=: u) = typ t == typeOf (undefined :: ItFun)

main = do
  let sig = renumber sig1
      bg = dialoop (constants sig)
  (props, sig) <- explore bg sig
  let sig' = renumber (sig `mappend` sig2 `mappend` sig3)
      bg' = comp (constants sig')
  explore (bg ++ bg' ++ props) sig'

--main = quickSpec (sig1 `mappend` sig2 `mappend` sig3)

timeout = 60

upTo :: (Int -> a -> IO a) -> Int -> a -> IO a
upTo f n x = go n x
  where
    go m x | m > n = return x
    go m x = f m x >>= go (m+1)

shrinkProof :: Signature -> [Simp] -> [Prop] -> [Prop] -> IO [Prop]
shrinkProof sig simp bg props =
  upTo (\n props -> shrinkProof1 n (reverse props)) timeout props
  where
    shrinkProof1 n [] = return []
    shrinkProof1 n (goal:props) = shrinkProof' n sig simp bg [goal] props

shrinkProof' :: Int -> Signature -> [Simp] -> [Prop] -> [Prop] -> [Prop] -> IO [Prop]
shrinkProof' timeout sig simp bg goals [] = return goals
shrinkProof' timeout sig simp bg goals (p:ps) = do
  res <- allProvable timeout sig simp (bg ++ ps) goals
  case res of
    True -> do
      putStrLn ("Didn't need " ++ prettyShow p)
      shrinkProof' timeout sig simp bg goals ps
    False -> do
      putStrLn ("Needed " ++ prettyShow p)
      shrinkProof' timeout sig simp bg (p:goals) ps

establish :: Int -> Signature -> [Simp] -> [Prop] -> [Prop] -> IO [Prop]
establish timeout sig simp bg ps = do
  new <- establish1 timeout sig simp bg [] ps
  let bg' = bg ++ new
  case new of
    [] -> do
      putStrLn ("Proved following laws:")
      mapM_ prettyPrint bg'
      return bg'
    _ -> do
      putStrLn "Loop!\n"
      establish timeout sig simp bg' (ps Data.List.\\ new)

type Simp = Signature -> Prop -> Maybe Prop

establish1 :: Int -> Signature -> [Simp] -> [Prop] -> [Prop] -> [Prop] -> IO [Prop]
establish1 timeout sig simp bg new [] = return new
establish1 timeout sig simp bg new (p:ps) = do
  res <- provable timeout sig simp (bg ++ new) p
  case res of
    True -> do
      putStrLn ("Proved " ++ prettyShow p)
      establish1 timeout sig simp bg (new ++ [p]) ps
    False -> do
      putStrLn ("Failed to prove " ++ prettyShow (sep [pretty p <+> text "=>", nest 2 (pretty [ f sig p | f <- simp ])]))
      establish1 timeout sig simp bg new ps

provable1 :: Int -> Signature -> Simp -> [Prop] -> Prop -> IO Bool
provable1 timeout sig simp bg p = do
  let bg' = catMaybes (map (fmap strip . simp sig) bg)
      strip = fmap (mapTerm stripCon stripVar)
      stripCon c = TermConstant c (typ c)
      stripVar x = PruningVariable (number x)
      skolemise = substf (\x -> Fun (SkolemVariable (stripVar x)) [])
  case simp sig p of
    Nothing -> return False
    Just p' ->
      liftIO $ pruner (Waldmeister timeout) bg' (skolemise (strip p'))

provable :: Int -> Signature -> [Simp] -> [Prop] -> Prop -> IO Bool
provable timeout sig [] bg p = return False
provable timeout sig (simp:simps) bg p = do
  rest <- provable1 timeout sig simp bg p
  case rest of
    True -> return True
    False -> provable timeout sig simps bg p

allProvable :: Int -> Signature -> [Simp] -> [Prop] -> [Prop] -> IO Bool
allProvable _ _ _ _ [] = return True
allProvable timeout sig simp ps (q:qs) = do
  res <- provable timeout sig simp ps q
  case res of
    False -> return False
    True -> allProvable timeout sig simp (ps ++ [q]) qs

newtype Cayley = Cayley Int deriving (Eq, Ord, Show, CoArbitrary)

cayley = map Cayley [1..81]

instance Group Cayley where
  Cayley x `op` Cayley y = Cayley (Map.findWithDefault undefined (x, y) tablemap)
  ident = head [ x | x <- cayley, and [ x `op` y == y && y `op` x == y | y <- cayley ] ]
  inv x = head [ y | y <- cayley, x `op` y == ident && y `op` x == ident ]

instance Arbitrary Cayley where arbitrary = fmap Cayley (choose (1, 81))

tablemap :: Map.Map (Int, Int) Int
tablemap = Map.fromList [((i, j), k) | (i, row) <- zip [1..] table, (j, k) <- zip [1..] row]

table :: [[Int]]
table =
  [ [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
        36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
        71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81 ], [ 2, 3, 1, 5, 6, 4, 8, 9, 7, 11, 12, 10, 14, 15, 13, 17, 18, 16, 20, 21, 19, 23,
        24, 22, 26, 27, 25, 29, 30, 28, 32, 33, 31, 35, 36, 34, 38, 39, 37, 41, 42, 40, 44, 45, 43, 47, 48, 46, 50, 51, 49, 53, 54, 52, 56, 57, 55,
        59, 60, 58, 62, 63, 61, 65, 66, 64, 68, 69, 67, 71, 72, 70, 74, 75, 73, 77, 78, 76, 80, 81, 79 ],
    [ 3, 1, 2, 6, 4, 5, 9, 7, 8, 12, 10, 11, 15, 13, 14, 18, 16, 17, 21, 19, 20, 24, 22, 23, 27, 25, 26, 30, 28, 29, 33, 31,
        32, 36, 34, 35, 39, 37, 38, 42, 40, 41, 45, 43, 44, 48, 46, 47, 51, 49, 50, 54, 52, 53, 57, 55, 56, 60, 58, 59, 63, 61, 62, 66, 64, 65, 69,
        67, 68, 72, 70, 71, 75, 73, 74, 78, 76, 77, 81, 79, 80 ], [ 4, 5, 6, 13, 14, 15, 16, 17, 18, 19, 20, 21, 2, 3, 1, 31, 32, 33, 34,
        35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 8, 9, 7, 11, 12, 10, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 23, 24, 22, 26,
        27, 25, 29, 30, 28, 70, 71, 72, 73, 74, 75, 76, 77, 78, 47, 48, 46, 50, 51, 49, 79, 80, 81, 68, 69, 67 ],
    [ 5, 6, 4, 14, 15, 13, 17, 18, 16, 20, 21, 19, 3, 1, 2, 32, 33, 31, 35, 36, 34, 38, 39, 37, 41, 42, 40, 44, 45, 43, 9, 7,
        8, 12, 10, 11, 53, 54, 52, 56, 57, 55, 59, 60, 58, 62, 63, 61, 65, 66, 64, 24, 22, 23, 27, 25, 26, 30, 28, 29, 71, 72, 70, 74, 75, 73, 77,
        78, 76, 48, 46, 47, 51, 49, 50, 80, 81, 79, 69, 67, 68 ], [ 6, 4, 5, 15, 13, 14, 18, 16, 17, 21, 19, 20, 1, 2, 3, 33, 31, 32, 36,
        34, 35, 39, 37, 38, 42, 40, 41, 45, 43, 44, 7, 8, 9, 10, 11, 12, 54, 52, 53, 57, 55, 56, 60, 58, 59, 63, 61, 62, 66, 64, 65, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 72, 70, 71, 75, 73, 74, 78, 76, 77, 46, 47, 48, 49, 50, 51, 81, 79, 80, 67, 68, 69 ],
    [ 7, 8, 9, 16, 17, 18, 22, 23, 24, 25, 26, 27, 31, 32, 33, 37, 38, 39, 41, 42, 40, 1, 2, 3, 46, 47, 48, 49, 50, 51, 52, 53,
        54, 57, 55, 56, 4, 5, 6, 62, 63, 61, 66, 64, 65, 10, 11, 12, 67, 68, 69, 13, 14, 15, 72, 70, 71, 74, 75, 73, 20, 21, 19, 78, 76, 77, 28, 29,
        30, 36, 34, 35, 80, 81, 79, 45, 43, 44, 59, 60, 58 ], [ 8, 9, 7, 17, 18, 16, 23, 24, 22, 26, 27, 25, 32, 33, 31, 38, 39, 37, 42, 40,
        41, 2, 3, 1, 47, 48, 46, 50, 51, 49, 53, 54, 52, 55, 56, 57, 5, 6, 4, 63, 61, 62, 64, 65, 66, 11, 12, 10, 68, 69, 67, 14, 15, 13, 70, 71,
        72, 75, 73, 74, 21, 19, 20, 76, 77, 78, 29, 30, 28, 34, 35, 36, 81, 79, 80, 43, 44, 45, 60, 58, 59 ],
    [ 9, 7, 8, 18, 16, 17, 24, 22, 23, 27, 25, 26, 33, 31, 32, 39, 37, 38, 40, 41, 42, 3, 1, 2, 48, 46, 47, 51, 49, 50, 54, 52, 53,
        56, 57, 55, 6, 4, 5, 61, 62, 63, 65, 66, 64, 12, 10, 11, 69, 67, 68, 15, 13, 14, 71, 72, 70, 73, 74, 75, 19, 20, 21, 77, 78, 76, 30, 28, 29,
        35, 36, 34, 79, 80, 81, 44, 45, 43, 58, 59, 60 ], [ 10, 11, 12, 19, 20, 21, 26, 27, 25, 28, 29, 30, 34, 35, 36, 40, 41, 42, 43, 44, 45,
        48, 46, 47, 50, 51, 49, 3, 1, 2, 57, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 66, 6, 4, 5, 69, 67, 68, 7, 8, 9, 71, 72, 70, 75, 73,
        74, 15, 13, 14, 76, 77, 78, 18, 16, 17, 23, 24, 22, 80, 81, 79, 32, 33, 31, 39, 37, 38, 52, 53, 54 ],
    [ 11, 12, 10, 20, 21, 19, 27, 25, 26, 29, 30, 28, 35, 36, 34, 41, 42, 40, 44, 45, 43, 46, 47, 48, 51, 49, 50, 1, 2, 3, 55, 56, 57,
        59, 60, 58, 62, 63, 61, 65, 66, 64, 4, 5, 6, 67, 68, 69, 8, 9, 7, 72, 70, 71, 73, 74, 75, 13, 14, 15, 77, 78, 76, 16, 17, 18, 24, 22, 23, 81,
        79, 80, 33, 31, 32, 37, 38, 39, 53, 54, 52 ], [ 12, 10, 11, 21, 19, 20, 25, 26, 27, 30, 28, 29, 36, 34, 35, 42, 40, 41, 45, 43, 44, 47,
        48, 46, 49, 50, 51, 2, 3, 1, 56, 57, 55, 60, 58, 59, 63, 61, 62, 66, 64, 65, 5, 6, 4, 68, 69, 67, 9, 7, 8, 70, 71, 72, 74, 75, 73,
        14, 15, 13, 78, 76, 77, 17, 18, 16, 22, 23, 24, 79, 80, 81, 31, 32, 33, 38, 39, 37, 54, 52, 53 ],
    [ 13, 14, 15, 2, 3, 1, 31, 32, 33, 34, 35, 36, 5, 6, 4, 8, 9, 7, 11, 12, 10, 52, 53, 54, 55, 56, 57, 58, 59, 60, 17, 18, 16,
        20, 21, 19, 23, 24, 22, 26, 27, 25, 29, 30, 28, 70, 71, 72, 73, 74, 75, 38, 39, 37, 41, 42, 40, 44, 45, 43, 47, 48, 46, 50, 51, 49, 79, 80,
        81, 62, 63, 61, 65, 66, 64, 68, 69, 67, 77, 78, 76 ], [ 14, 15, 13, 3, 1, 2, 32, 33, 31, 35, 36, 34, 6, 4, 5, 9, 7, 8, 12, 10,
        11, 53, 54, 52, 56, 57, 55, 59, 60, 58, 18, 16, 17, 21, 19, 20, 24, 22, 23, 27, 25, 26, 30, 28, 29, 71, 72, 70, 74, 75, 73, 39, 37, 38, 42,
        40, 41, 45, 43, 44, 48, 46, 47, 51, 49, 50, 80, 81, 79, 63, 61, 62, 66, 64, 65, 69, 67, 68, 78, 76, 77 ],
    [ 15, 13, 14, 1, 2, 3, 33, 31, 32, 36, 34, 35, 4, 5, 6, 7, 8, 9, 10, 11, 12, 54, 52, 53, 57, 55, 56, 60, 58, 59, 16, 17,
        18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 72, 70, 71, 75, 73, 74, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 81,
        79, 80, 61, 62, 63, 64, 65, 66, 67, 68, 69, 76, 77, 78 ], [ 16, 17, 18, 31, 32, 33, 37, 38, 39, 42, 40, 41, 8, 9, 7, 52, 53, 54, 55,
        56, 57, 4, 5, 6, 63, 61, 62, 65, 66, 64, 23, 24, 22, 27, 25, 26, 13, 14, 15, 70, 71, 72, 73, 74, 75, 21, 19, 20, 77, 78, 76, 2, 3, 1, 48,
        46, 47, 49, 50, 51, 34, 35, 36, 79, 80, 81, 44, 45, 43, 12, 10, 11, 67, 68, 69, 58, 59, 60, 28, 29, 30 ],
    [ 17, 18, 16, 32, 33, 31, 38, 39, 37, 40, 41, 42, 9, 7, 8, 53, 54, 52, 56, 57, 55, 5, 6, 4, 61, 62, 63, 66, 64, 65, 24, 22, 23,
        25, 26, 27, 14, 15, 13, 71, 72, 70, 74, 75, 73, 19, 20, 21, 78, 76, 77, 3, 1, 2, 46, 47, 48, 50, 51, 49, 35, 36, 34, 80, 81, 79, 45, 43, 44,
        10, 11, 12, 68, 69, 67, 59, 60, 58, 29, 30, 28 ], [ 18, 16, 17, 33, 31, 32, 39, 37, 38, 41, 42, 40, 7, 8, 9, 54, 52, 53, 57, 55, 56,
        6, 4, 5, 62, 63, 61, 64, 65, 66, 22, 23, 24, 26, 27, 25, 15, 13, 14, 72, 70, 71, 75, 73, 74, 20, 21, 19, 76, 77, 78, 1, 2, 3, 47, 48, 46, 51,
        49, 50, 36, 34, 35, 81, 79, 80, 43, 44, 45, 11, 12, 10, 69, 67, 68, 60, 58, 59, 30, 28, 29 ],
    [ 19, 20, 21, 34, 35, 36, 42, 40, 41, 43, 44, 45, 11, 12, 10, 56, 57, 55, 58, 59, 60, 62, 63, 61, 66, 64, 65, 6, 4, 5, 26, 27, 25,
        29, 30, 28, 72, 70, 71, 74, 75, 73, 15, 13, 14, 77, 78, 76, 17, 18, 16, 47, 48, 46, 50, 51, 49, 1, 2, 3, 81, 79, 80, 31, 32, 33, 37, 38, 39,
        68, 69, 67, 7, 8, 9, 53, 54, 52, 22, 23, 24 ], [ 20, 21, 19, 35, 36, 34, 40, 41, 42, 44, 45, 43, 12, 10, 11, 57, 55, 56, 59, 60, 58,
        63, 61, 62, 64, 65, 66, 4, 5, 6, 27, 25, 26, 30, 28, 29, 70, 71, 72, 75, 73, 74, 13, 14, 15, 78, 76, 77, 18, 16, 17, 48, 46, 47, 51, 49, 50,
        2, 3, 1, 79, 80, 81, 32, 33, 31, 38, 39, 37, 69, 67, 68, 8, 9, 7, 54, 52, 53, 23, 24, 22 ],
    [ 21, 19, 20, 36, 34, 35, 41, 42, 40, 45, 43, 44, 10, 11, 12, 55, 56, 57, 60, 58, 59, 61, 62, 63, 65, 66, 64, 5, 6, 4, 25, 26,
        27, 28, 29, 30, 71, 72, 70, 73, 74, 75, 14, 15, 13, 76, 77, 78, 16, 17, 18, 46, 47, 48, 49, 50, 51, 3, 1, 2, 80, 81, 79, 33, 31, 32, 39, 37,
        38, 67, 68, 69, 9, 7, 8, 52, 53, 54, 24, 22, 23 ], [ 22, 23, 24, 37, 38, 39, 1, 2, 3, 46, 47, 48, 52, 53, 54, 4, 5, 6, 63, 61,
        62, 7, 8, 9, 10, 11, 12, 67, 68, 69, 13, 14, 15, 71, 72, 70, 16, 17, 18, 21, 19, 20, 77, 78, 76, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 36,
        34, 81, 79, 80, 42, 40, 41, 44, 45, 43, 49, 50, 51, 56, 57, 55, 60, 58, 59, 65, 66, 64, 75, 73, 74 ],
    [ 23, 24, 22, 38, 39, 37, 2, 3, 1, 47, 48, 46, 53, 54, 52, 5, 6, 4, 61, 62, 63, 8, 9, 7, 11, 12, 10, 68, 69, 67, 14, 15,
        13, 72, 70, 71, 17, 18, 16, 19, 20, 21, 78, 76, 77, 26, 27, 25, 29, 30, 28, 32, 33, 31, 36, 34, 35, 79, 80, 81, 40, 41, 42, 45, 43, 44, 50,
        51, 49, 57, 55, 56, 58, 59, 60, 66, 64, 65, 73, 74, 75 ], [ 24, 22, 23, 39, 37, 38, 3, 1, 2, 48, 46, 47, 54, 52, 53, 6, 4, 5, 62,
        63, 61, 9, 7, 8, 12, 10, 11, 69, 67, 68, 15, 13, 14, 70, 71, 72, 18, 16, 17, 20, 21, 19, 76, 77, 78, 27, 25, 26, 30, 28, 29, 33, 31, 32, 34,
        35, 36, 80, 81, 79, 41, 42, 40, 43, 44, 45, 51, 49, 50, 55, 56, 57, 59, 60, 58, 64, 65, 66, 74, 75, 73 ],
    [ 25, 26, 27, 40, 41, 42, 47, 48, 46, 49, 50, 51, 55, 56, 57, 61, 62, 63, 65, 66, 64, 12, 10, 11, 68, 69, 67, 9, 7, 8, 72, 70, 71,
        75, 73, 74, 19, 20, 21, 77, 78, 76, 17, 18, 16, 30, 28, 29, 22, 23, 24, 35, 36, 34, 80, 81, 79, 31, 32, 33, 44, 45, 43, 38, 39, 37, 2, 3, 1,
        58, 59, 60, 54, 52, 53, 5, 6, 4, 14, 15, 13 ], [ 26, 27, 25, 41, 42, 40, 48, 46, 47, 50, 51, 49, 56, 57, 55, 62, 63, 61, 66, 64, 65,
        10, 11, 12, 69, 67, 68, 7, 8, 9, 70, 71, 72, 73, 74, 75, 20, 21, 19, 78, 76, 77, 18, 16, 17, 28, 29, 30, 23, 24, 22, 36, 34, 35, 81, 79, 80,
        32, 33, 31, 45, 43, 44, 39, 37, 38, 3, 1, 2, 59, 60, 58, 52, 53, 54, 6, 4, 5, 15, 13, 14 ],
    [ 27, 25, 26, 42, 40, 41, 46, 47, 48, 51, 49, 50, 57, 55, 56, 63, 61, 62, 64, 65, 66, 11, 12, 10, 67, 68, 69, 8, 9, 7, 71, 72,
        70, 74, 75, 73, 21, 19, 20, 76, 77, 78, 16, 17, 18, 29, 30, 28, 24, 22, 23, 34, 35, 36, 79, 80, 81, 33, 31, 32, 43, 44, 45, 37, 38, 39, 1, 2,
        3, 60, 58, 59, 53, 54, 52, 4, 5, 6, 13, 14, 15 ], [ 28, 29, 30, 43, 44, 45, 51, 49, 50, 3, 1, 2, 58, 59, 60, 64, 65, 66, 6, 4,
        5, 68, 69, 67, 8, 9, 7, 12, 10, 11, 74, 75, 73, 15, 13, 14, 76, 77, 78, 18, 16, 17, 21, 19, 20, 22, 23, 24, 26, 27, 25, 81, 79, 80, 31, 32,
        33, 36, 34, 35, 39, 37, 38, 42, 40, 41, 46, 47, 48, 53, 54, 52, 55, 56, 57, 63, 61, 62, 71, 72, 70 ],
    [ 29, 30, 28, 44, 45, 43, 49, 50, 51, 1, 2, 3, 59, 60, 58, 65, 66, 64, 4, 5, 6, 69, 67, 68, 9, 7, 8, 10, 11, 12, 75, 73, 74,
        13, 14, 15, 77, 78, 76, 16, 17, 18, 19, 20, 21, 23, 24, 22, 27, 25, 26, 79, 80, 81, 32, 33, 31, 34, 35, 36, 37, 38, 39, 40, 41, 42, 47, 48,
        46, 54, 52, 53, 56, 57, 55, 61, 62, 63, 72, 70, 71 ], [ 30, 28, 29, 45, 43, 44, 50, 51, 49, 2, 3, 1, 60, 58, 59, 66, 64, 65, 5, 6,
        4, 67, 68, 69, 7, 8, 9, 11, 12, 10, 73, 74, 75, 14, 15, 13, 78, 76, 77, 17, 18, 16, 20, 21, 19, 24, 22, 23, 25, 26, 27, 80, 81, 79, 33, 31,
        32, 35, 36, 34, 38, 39, 37, 41, 42, 40, 48, 46, 47, 52, 53, 54, 57, 55, 56, 62, 63, 61, 70, 71, 72 ],
    [ 31, 32, 33, 8, 9, 7, 52, 53, 54, 56, 57, 55, 17, 18, 16, 23, 24, 22, 25, 26, 27, 13, 14, 15, 71, 72, 70, 75, 73, 74, 38, 39,
        37, 41, 42, 40, 2, 3, 1, 46, 47, 48, 51, 49, 50, 35, 36, 34, 81, 79, 80, 5, 6, 4, 62, 63, 61, 65, 66, 64, 10, 11, 12, 69, 67, 68, 60, 58, 59,
        20, 21, 19, 77, 78, 76, 30, 28, 29, 44, 45, 43 ], [ 32, 33, 31, 9, 7, 8, 53, 54, 52, 57, 55, 56, 18, 16, 17, 24, 22, 23, 26, 27, 25,
        14, 15, 13, 72, 70, 71, 73, 74, 75, 39, 37, 38, 42, 40, 41, 3, 1, 2, 47, 48, 46, 49, 50, 51, 36, 34, 35, 79, 80, 81, 6, 4, 5, 63, 61, 62,
        66, 64, 65, 11, 12, 10, 67, 68, 69, 58, 59, 60, 21, 19, 20, 78, 76, 77, 28, 29, 30, 45, 43, 44 ],
    [ 33, 31, 32, 7, 8, 9, 54, 52, 53, 55, 56, 57, 16, 17, 18, 22, 23, 24, 27, 25, 26, 15, 13, 14, 70, 71, 72, 74, 75, 73, 37, 38, 39,
        40, 41, 42, 1, 2, 3, 48, 46, 47, 50, 51, 49, 34, 35, 36, 80, 81, 79, 4, 5, 6, 61, 62, 63, 64, 65, 66, 12, 10, 11, 68, 69, 67, 59, 60, 58, 19,
        20, 21, 76, 77, 78, 29, 30, 28, 43, 44, 45 ], [ 34, 35, 36, 11, 12, 10, 55, 56, 57, 58, 59, 60, 20, 21, 19, 25, 26, 27, 29, 30, 28, 70,
        71, 72, 73, 74, 75, 15, 13, 14, 42, 40, 41, 44, 45, 43, 48, 46, 47, 49, 50, 51, 1, 2, 3, 79, 80, 81, 33, 31, 32, 61, 62, 63, 66, 64, 65,
        4, 5, 6, 69, 67, 68, 9, 7, 8, 54, 52, 53, 76, 77, 78, 17, 18, 16, 23, 24, 22, 39, 37, 38 ],
    [ 35, 36, 34, 12, 10, 11, 56, 57, 55, 59, 60, 58, 21, 19, 20, 26, 27, 25, 30, 28, 29, 71, 72, 70, 74, 75, 73, 13, 14, 15, 40, 41, 42,
        45, 43, 44, 46, 47, 48, 50, 51, 49, 2, 3, 1, 80, 81, 79, 31, 32, 33, 62, 63, 61, 64, 65, 66, 5, 6, 4, 67, 68, 69, 7, 8, 9, 52, 53, 54, 77,
        78, 76, 18, 16, 17, 24, 22, 23, 37, 38, 39 ], [ 36, 34, 35, 10, 11, 12, 57, 55, 56, 60, 58, 59, 19, 20, 21, 27, 25, 26, 28, 29, 30, 72, 70,
        71, 75, 73, 74, 14, 15, 13, 41, 42, 40, 43, 44, 45, 47, 48, 46, 51, 49, 50, 3, 1, 2, 81, 79, 80, 32, 33, 31, 63, 61, 62, 65, 66, 64,
        6, 4, 5, 68, 69, 67, 8, 9, 7, 53, 54, 52, 78, 76, 77, 16, 17, 18, 22, 23, 24, 38, 39, 37 ],
    [ 37, 38, 39, 52, 53, 54, 4, 5, 6, 62, 63, 61, 23, 24, 22, 13, 14, 15, 70, 71, 72, 16, 17, 18, 20, 21, 19, 78, 76, 77, 2, 3, 1,
        46, 47, 48, 31, 32, 33, 34, 35, 36, 79, 80, 81, 41, 42, 40, 45, 43, 44, 8, 9, 7, 10, 11, 12, 69, 67, 68, 55, 56, 57, 58, 59, 60, 66, 64, 65,
        25, 26, 27, 30, 28, 29, 73, 74, 75, 51, 49, 50 ], [ 38, 39, 37, 53, 54, 52, 5, 6, 4, 63, 61, 62, 24, 22, 23, 14, 15, 13, 71, 72, 70,
        17, 18, 16, 21, 19, 20, 76, 77, 78, 3, 1, 2, 47, 48, 46, 32, 33, 31, 35, 36, 34, 80, 81, 79, 42, 40, 41, 43, 44, 45, 9, 7, 8, 11, 12, 10,
        67, 68, 69, 56, 57, 55, 59, 60, 58, 64, 65, 66, 26, 27, 25, 28, 29, 30, 74, 75, 73, 49, 50, 51 ],
    [ 39, 37, 38, 54, 52, 53, 6, 4, 5, 61, 62, 63, 22, 23, 24, 15, 13, 14, 72, 70, 71, 18, 16, 17, 19, 20, 21, 77, 78, 76, 1, 2, 3,
        48, 46, 47, 33, 31, 32, 36, 34, 35, 81, 79, 80, 40, 41, 42, 44, 45, 43, 7, 8, 9, 12, 10, 11, 68, 69, 67, 57, 55, 56, 60, 58, 59, 65, 66, 64,
        27, 25, 26, 29, 30, 28, 75, 73, 74, 50, 51, 49 ], [ 40, 41, 42, 55, 56, 57, 63, 61, 62, 66, 64, 65, 26, 27, 25, 71, 72, 70, 73, 74, 75,
        20, 21, 19, 77, 78, 76, 16, 17, 18, 47, 48, 46, 51, 49, 50, 36, 34, 35, 80, 81, 79, 33, 31, 32, 43, 44, 45, 39, 37, 38, 11, 12, 10, 69, 67,
        68, 9, 7, 8, 60, 58, 59, 52, 53, 54, 5, 6, 4, 30, 28, 29, 24, 22, 23, 14, 15, 13, 3, 1, 2 ],
    [ 41, 42, 40, 56, 57, 55, 61, 62, 63, 64, 65, 66, 27, 25, 26, 72, 70, 71, 74, 75, 73, 21, 19, 20, 78, 76, 77, 17, 18, 16, 48, 46,
        47, 49, 50, 51, 34, 35, 36, 81, 79, 80, 31, 32, 33, 44, 45, 43, 37, 38, 39, 12, 10, 11, 67, 68, 69, 7, 8, 9, 58, 59, 60, 53, 54, 52, 6, 4, 5,
        28, 29, 30, 22, 23, 24, 15, 13, 14, 1, 2, 3 ], [ 42, 40, 41, 57, 55, 56, 62, 63, 61, 65, 66, 64, 25, 26, 27, 70, 71, 72, 75, 73, 74,
        19, 20, 21, 76, 77, 78, 18, 16, 17, 46, 47, 48, 50, 51, 49, 35, 36, 34, 79, 80, 81, 32, 33, 31, 45, 43, 44, 38, 39, 37, 10, 11, 12, 68, 69,
        67, 8, 9, 7, 59, 60, 58, 54, 52, 53, 4, 5, 6, 29, 30, 28, 23, 24, 22, 13, 14, 15, 2, 3, 1 ],
    [ 43, 44, 45, 58, 59, 60, 65, 66, 64, 6, 4, 5, 29, 30, 28, 75, 73, 74, 15, 13, 14, 78, 76, 77, 16, 17, 18, 21, 19, 20, 50, 51,
        49, 1, 2, 3, 80, 81, 79, 32, 33, 31, 36, 34, 35, 38, 39, 37, 40, 41, 42, 68, 69, 67, 7, 8, 9, 10, 11, 12, 52, 53, 54, 56, 57, 55, 62, 63, 61,
        22, 23, 24, 25, 26, 27, 70, 71, 72, 46, 47, 48 ], [ 44, 45, 43, 59, 60, 58, 66, 64, 65, 4, 5, 6, 30, 28, 29, 73, 74, 75, 13, 14, 15,
        76, 77, 78, 17, 18, 16, 19, 20, 21, 51, 49, 50, 2, 3, 1, 81, 79, 80, 33, 31, 32, 34, 35, 36, 39, 37, 38, 41, 42, 40, 69, 67, 68, 8, 9, 7,
        11, 12, 10, 53, 54, 52, 57, 55, 56, 63, 61, 62, 23, 24, 22, 26, 27, 25, 71, 72, 70, 47, 48, 46 ],
    [ 45, 43, 44, 60, 58, 59, 64, 65, 66, 5, 6, 4, 28, 29, 30, 74, 75, 73, 14, 15, 13, 77, 78, 76, 18, 16, 17, 20, 21, 19, 49, 50, 51,
        3, 1, 2, 79, 80, 81, 31, 32, 33, 35, 36, 34, 37, 38, 39, 42, 40, 41, 67, 68, 69, 9, 7, 8, 12, 10, 11, 54, 52, 53, 55, 56, 57, 61, 62, 63, 24,
        22, 23, 27, 25, 26, 72, 70, 71, 48, 46, 47 ], [ 46, 47, 48, 61, 62, 63, 11, 12, 10, 67, 68, 69, 70, 71, 72, 19, 20, 21, 78, 76, 77, 27,
        25, 26, 29, 30, 28, 24, 22, 23, 36, 34, 35, 80, 81, 79, 40, 41, 42, 45, 43, 44, 37, 38, 39, 51, 49, 50, 1, 2, 3, 56, 57, 55, 58, 59, 60,
        53, 54, 52, 66, 64, 65, 4, 5, 6, 8, 9, 7, 75, 73, 74, 13, 14, 15, 16, 17, 18, 33, 31, 32 ],
    [ 47, 48, 46, 62, 63, 61, 12, 10, 11, 68, 69, 67, 71, 72, 70, 20, 21, 19, 76, 77, 78, 25, 26, 27, 30, 28, 29, 22, 23, 24, 34, 35,
        36, 81, 79, 80, 41, 42, 40, 43, 44, 45, 38, 39, 37, 49, 50, 51, 2, 3, 1, 57, 55, 56, 59, 60, 58, 54, 52, 53, 64, 65, 66, 5, 6, 4, 9, 7, 8,
        73, 74, 75, 14, 15, 13, 17, 18, 16, 31, 32, 33 ], [ 48, 46, 47, 63, 61, 62, 10, 11, 12, 69, 67, 68, 72, 70, 71, 21, 19, 20, 77, 78, 76,
        26, 27, 25, 28, 29, 30, 23, 24, 22, 35, 36, 34, 79, 80, 81, 42, 40, 41, 44, 45, 43, 39, 37, 38, 50, 51, 49, 3, 1, 2, 55, 56, 57, 60, 58,
        59, 52, 53, 54, 65, 66, 64, 6, 4, 5, 7, 8, 9, 74, 75, 73, 15, 13, 14, 18, 16, 17, 32, 33, 31 ],
    [ 49, 50, 51, 64, 65, 66, 69, 67, 68, 9, 7, 8, 73, 74, 75, 76, 77, 78, 16, 17, 18, 29, 30, 28, 23, 24, 22, 27, 25, 26, 80, 81,
        79, 32, 33, 31, 43, 44, 45, 37, 38, 39, 41, 42, 40, 1, 2, 3, 47, 48, 46, 60, 58, 59, 54, 52, 53, 55, 56, 57, 4, 5, 6, 62, 63, 61, 10, 11, 12,
        13, 14, 15, 71, 72, 70, 20, 21, 19, 36, 34, 35 ], [ 50, 51, 49, 65, 66, 64, 67, 68, 69, 7, 8, 9, 74, 75, 73, 77, 78, 76, 17, 18, 16,
        30, 28, 29, 24, 22, 23, 25, 26, 27, 81, 79, 80, 33, 31, 32, 44, 45, 43, 38, 39, 37, 42, 40, 41, 2, 3, 1, 48, 46, 47, 58, 59, 60, 52, 53, 54,
        56, 57, 55, 5, 6, 4, 63, 61, 62, 11, 12, 10, 14, 15, 13, 72, 70, 71, 21, 19, 20, 34, 35, 36 ],
    [ 51, 49, 50, 66, 64, 65, 68, 69, 67, 8, 9, 7, 75, 73, 74, 78, 76, 77, 18, 16, 17, 28, 29, 30, 22, 23, 24, 26, 27, 25, 79, 80,
        81, 31, 32, 33, 45, 43, 44, 39, 37, 38, 40, 41, 42, 3, 1, 2, 46, 47, 48, 59, 60, 58, 53, 54, 52, 57, 55, 56, 6, 4, 5, 61, 62, 63, 12, 10, 11,
        15, 13, 14, 70, 71, 72, 19, 20, 21, 35, 36, 34 ], [ 52, 53, 54, 23, 24, 22, 13, 14, 15, 72, 70, 71, 38, 39, 37, 2, 3, 1, 48, 46, 47,
        31, 32, 33, 36, 34, 35, 80, 81, 79, 5, 6, 4, 62, 63, 61, 8, 9, 7, 12, 10, 11, 67, 68, 69, 57, 55, 56, 59, 60, 58, 17, 18, 16, 20, 21, 19,
        77, 78, 76, 27, 25, 26, 28, 29, 30, 74, 75, 73, 41, 42, 40, 44, 45, 43, 49, 50, 51, 65, 66, 64 ],
    [ 53, 54, 52, 24, 22, 23, 14, 15, 13, 70, 71, 72, 39, 37, 38, 3, 1, 2, 46, 47, 48, 32, 33, 31, 34, 35, 36, 81, 79, 80, 6, 4, 5,
        63, 61, 62, 9, 7, 8, 10, 11, 12, 68, 69, 67, 55, 56, 57, 60, 58, 59, 18, 16, 17, 21, 19, 20, 78, 76, 77, 25, 26, 27, 29, 30, 28, 75, 73, 74,
        42, 40, 41, 45, 43, 44, 50, 51, 49, 66, 64, 65 ], [ 54, 52, 53, 22, 23, 24, 15, 13, 14, 71, 72, 70, 37, 38, 39, 1, 2, 3, 47, 48, 46,
        33, 31, 32, 35, 36, 34, 79, 80, 81, 4, 5, 6, 61, 62, 63, 7, 8, 9, 11, 12, 10, 69, 67, 68, 56, 57, 55, 58, 59, 60, 16, 17, 18, 19, 20, 21,
        76, 77, 78, 26, 27, 25, 30, 28, 29, 73, 74, 75, 40, 41, 42, 43, 44, 45, 51, 49, 50, 64, 65, 66 ],
    [ 55, 56, 57, 26, 27, 25, 70, 71, 72, 74, 75, 73, 41, 42, 40, 46, 47, 48, 49, 50, 51, 34, 35, 36, 80, 81, 79, 32, 33, 31, 63, 61, 62,
        65, 66, 64, 12, 10, 11, 69, 67, 68, 8, 9, 7, 59, 60, 58, 53, 54, 52, 19, 20, 21, 78, 76, 77, 16, 17, 18, 29, 30, 28, 22, 23, 24, 14, 15, 13,
        43, 44, 45, 38, 39, 37, 3, 1, 2, 6, 4, 5 ], [ 56, 57, 55, 27, 25, 26, 71, 72, 70, 75, 73, 74, 42, 40, 41, 47, 48, 46, 50, 51, 49,
        35, 36, 34, 81, 79, 80, 33, 31, 32, 61, 62, 63, 66, 64, 65, 10, 11, 12, 67, 68, 69, 9, 7, 8, 60, 58, 59, 54, 52, 53, 20, 21, 19, 76, 77, 78,
        17, 18, 16, 30, 28, 29, 23, 24, 22, 15, 13, 14, 44, 45, 43, 39, 37, 38, 1, 2, 3, 4, 5, 6 ],
    [ 57, 55, 56, 25, 26, 27, 72, 70, 71, 73, 74, 75, 40, 41, 42, 48, 46, 47, 51, 49, 50, 36, 34, 35, 79, 80, 81, 31, 32, 33, 62, 63,
        61, 64, 65, 66, 11, 12, 10, 68, 69, 67, 7, 8, 9, 58, 59, 60, 52, 53, 54, 21, 19, 20, 77, 78, 76, 18, 16, 17, 28, 29, 30, 24, 22, 23, 13, 14,
        15, 45, 43, 44, 37, 38, 39, 2, 3, 1, 5, 6, 4 ], [ 58, 59, 60, 29, 30, 28, 73, 74, 75, 15, 13, 14, 44, 45, 43, 51, 49, 50, 1, 2,
        3, 79, 80, 81, 33, 31, 32, 36, 34, 35, 64, 65, 66, 4, 5, 6, 67, 68, 69, 8, 9, 7, 10, 11, 12, 54, 52, 53, 57, 55, 56, 78, 76, 77, 18, 16, 17,
        19, 20, 21, 24, 22, 23, 26, 27, 25, 72, 70, 71, 38, 39, 37, 42, 40, 41, 48, 46, 47, 62, 63, 61 ],
    [ 59, 60, 58, 30, 28, 29, 74, 75, 73, 13, 14, 15, 45, 43, 44, 49, 50, 51, 2, 3, 1, 80, 81, 79, 31, 32, 33, 34, 35, 36, 65, 66, 64,
        5, 6, 4, 68, 69, 67, 9, 7, 8, 11, 12, 10, 52, 53, 54, 55, 56, 57, 76, 77, 78, 16, 17, 18, 20, 21, 19, 22, 23, 24, 27, 25, 26, 70, 71, 72, 39,
        37, 38, 40, 41, 42, 46, 47, 48, 63, 61, 62 ], [ 60, 58, 59, 28, 29, 30, 75, 73, 74, 14, 15, 13, 43, 44, 45, 50, 51, 49, 3, 1, 2, 81,
        79, 80, 32, 33, 31, 35, 36, 34, 66, 64, 65, 6, 4, 5, 69, 67, 68, 7, 8, 9, 12, 10, 11, 53, 54, 52, 56, 57, 55, 77, 78, 76, 17, 18, 16, 21,
        19, 20, 23, 24, 22, 25, 26, 27, 71, 72, 70, 37, 38, 39, 41, 42, 40, 47, 48, 46, 61, 62, 63 ],
    [ 61, 62, 63, 70, 71, 72, 21, 19, 20, 77, 78, 76, 47, 48, 46, 35, 36, 34, 79, 80, 81, 41, 42, 40, 43, 44, 45, 38, 39, 37, 11, 12, 10,
        67, 68, 69, 57, 55, 56, 59, 60, 58, 54, 52, 53, 66, 64, 65, 4, 5, 6, 26, 27, 25, 28, 29, 30, 23, 24, 22, 75, 73, 74, 13, 14, 15, 18, 16, 17,
        49, 50, 51, 2, 3, 1, 32, 33, 31, 8, 9, 7 ], [ 62, 63, 61, 71, 72, 70, 19, 20, 21, 78, 76, 77, 48, 46, 47, 36, 34, 35, 80, 81, 79,
        42, 40, 41, 44, 45, 43, 39, 37, 38, 12, 10, 11, 68, 69, 67, 55, 56, 57, 60, 58, 59, 52, 53, 54, 64, 65, 66, 5, 6, 4, 27, 25, 26, 29, 30, 28,
        24, 22, 23, 73, 74, 75, 14, 15, 13, 16, 17, 18, 50, 51, 49, 3, 1, 2, 33, 31, 32, 9, 7, 8 ],
    [ 63, 61, 62, 72, 70, 71, 20, 21, 19, 76, 77, 78, 46, 47, 48, 34, 35, 36, 81, 79, 80, 40, 41, 42, 45, 43, 44, 37, 38, 39, 10, 11,
        12, 69, 67, 68, 56, 57, 55, 58, 59, 60, 53, 54, 52, 65, 66, 64, 6, 4, 5, 25, 26, 27, 30, 28, 29, 22, 23, 24, 74, 75, 73, 15, 13, 14, 17, 18,
        16, 51, 49, 50, 1, 2, 3, 31, 32, 33, 7, 8, 9 ], [ 64, 65, 66, 73, 74, 75, 77, 78, 76, 17, 18, 16, 50, 51, 49, 81, 79, 80, 33, 31,
        32, 45, 43, 44, 39, 37, 38, 40, 41, 42, 68, 69, 67, 8, 9, 7, 59, 60, 58, 53, 54, 52, 57, 55, 56, 4, 5, 6, 62, 63, 61, 29, 30, 28, 23, 24, 22,
        27, 25, 26, 13, 14, 15, 71, 72, 70, 21, 19, 20, 2, 3, 1, 48, 46, 47, 34, 35, 36, 12, 10, 11 ],
    [ 65, 66, 64, 74, 75, 73, 78, 76, 77, 18, 16, 17, 51, 49, 50, 79, 80, 81, 31, 32, 33, 43, 44, 45, 37, 38, 39, 41, 42, 40, 69, 67,
        68, 9, 7, 8, 60, 58, 59, 54, 52, 53, 55, 56, 57, 5, 6, 4, 63, 61, 62, 30, 28, 29, 24, 22, 23, 25, 26, 27, 14, 15, 13, 72, 70, 71, 19, 20, 21,
        3, 1, 2, 46, 47, 48, 35, 36, 34, 10, 11, 12 ], [ 66, 64, 65, 75, 73, 74, 76, 77, 78, 16, 17, 18, 49, 50, 51, 80, 81, 79, 32, 33, 31,
        44, 45, 43, 38, 39, 37, 42, 40, 41, 67, 68, 69, 7, 8, 9, 58, 59, 60, 52, 53, 54, 56, 57, 55, 6, 4, 5, 61, 62, 63, 28, 29, 30, 22, 23, 24,
        26, 27, 25, 15, 13, 14, 70, 71, 72, 20, 21, 19, 1, 2, 3, 47, 48, 46, 36, 34, 35, 11, 12, 10 ],
    [ 67, 68, 69, 76, 77, 78, 30, 28, 29, 24, 22, 23, 79, 80, 81, 43, 44, 45, 38, 39, 37, 50, 51, 49, 2, 3, 1, 48, 46, 47, 59, 60, 58,
        52, 53, 54, 64, 65, 66, 5, 6, 4, 61, 62, 63, 7, 8, 9, 11, 12, 10, 75, 73, 74, 14, 15, 13, 71, 72, 70, 17, 18, 16, 19, 20, 21, 25, 26, 27, 33,
        31, 32, 36, 34, 35, 40, 41, 42, 55, 56, 57 ], [ 68, 69, 67, 77, 78, 76, 28, 29, 30, 22, 23, 24, 80, 81, 79, 44, 45, 43, 39, 37, 38, 51,
        49, 50, 3, 1, 2, 46, 47, 48, 60, 58, 59, 53, 54, 52, 65, 66, 64, 6, 4, 5, 62, 63, 61, 8, 9, 7, 12, 10, 11, 73, 74, 75, 15, 13, 14,
        72, 70, 71, 18, 16, 17, 20, 21, 19, 26, 27, 25, 31, 32, 33, 34, 35, 36, 41, 42, 40, 56, 57, 55 ],
    [ 69, 67, 68, 78, 76, 77, 29, 30, 28, 23, 24, 22, 81, 79, 80, 45, 43, 44, 37, 38, 39, 49, 50, 51, 1, 2, 3, 47, 48, 46, 58, 59, 60,
        54, 52, 53, 66, 64, 65, 4, 5, 6, 63, 61, 62, 9, 7, 8, 10, 11, 12, 74, 75, 73, 13, 14, 15, 70, 71, 72, 16, 17, 18, 21, 19, 20, 27, 25, 26, 32,
        33, 31, 35, 36, 34, 42, 40, 41, 57, 55, 56 ], [ 70, 71, 72, 47, 48, 46, 34, 35, 36, 81, 79, 80, 62, 63, 61, 10, 11, 12, 69, 67, 68, 55,
        56, 57, 60, 58, 59, 52, 53, 54, 21, 19, 20, 77, 78, 76, 27, 25, 26, 29, 30, 28, 24, 22, 23, 75, 73, 74, 13, 14, 15, 40, 41, 42, 45, 43, 44,
        37, 38, 39, 49, 50, 51, 2, 3, 1, 31, 32, 33, 64, 65, 66, 5, 6, 4, 7, 8, 9, 18, 16, 17 ],
    [ 71, 72, 70, 48, 46, 47, 35, 36, 34, 79, 80, 81, 63, 61, 62, 11, 12, 10, 67, 68, 69, 56, 57, 55, 58, 59, 60, 53, 54, 52, 19, 20,
        21, 78, 76, 77, 25, 26, 27, 30, 28, 29, 22, 23, 24, 73, 74, 75, 14, 15, 13, 41, 42, 40, 43, 44, 45, 38, 39, 37, 50, 51, 49, 3, 1, 2, 32, 33,
        31, 65, 66, 64, 6, 4, 5, 8, 9, 7, 16, 17, 18 ], [ 72, 70, 71, 46, 47, 48, 36, 34, 35, 80, 81, 79, 61, 62, 63, 12, 10, 11, 68, 69,
        67, 57, 55, 56, 59, 60, 58, 54, 52, 53, 20, 21, 19, 76, 77, 78, 26, 27, 25, 28, 29, 30, 23, 24, 22, 74, 75, 73, 15, 13, 14, 42, 40, 41, 44,
        45, 43, 39, 37, 38, 51, 49, 50, 1, 2, 3, 33, 31, 32, 66, 64, 65, 4, 5, 6, 9, 7, 8, 17, 18, 16 ],
    [ 73, 74, 75, 50, 51, 49, 79, 80, 81, 31, 32, 33, 65, 66, 64, 69, 67, 68, 9, 7, 8, 58, 59, 60, 52, 53, 54, 56, 57, 55, 76, 77,
        78, 16, 17, 18, 28, 29, 30, 22, 23, 24, 26, 27, 25, 13, 14, 15, 71, 72, 70, 45, 43, 44, 39, 37, 38, 40, 41, 42, 2, 3, 1, 48, 46, 47, 35, 36,
        34, 5, 6, 4, 63, 61, 62, 10, 11, 12, 20, 21, 19 ], [ 74, 75, 73, 51, 49, 50, 80, 81, 79, 32, 33, 31, 66, 64, 65, 67, 68, 69, 7, 8,
        9, 59, 60, 58, 53, 54, 52, 57, 55, 56, 77, 78, 76, 17, 18, 16, 29, 30, 28, 23, 24, 22, 27, 25, 26, 14, 15, 13, 72, 70, 71, 43, 44, 45, 37,
        38, 39, 41, 42, 40, 3, 1, 2, 46, 47, 48, 36, 34, 35, 6, 4, 5, 61, 62, 63, 11, 12, 10, 21, 19, 20 ],
    [ 75, 73, 74, 49, 50, 51, 81, 79, 80, 33, 31, 32, 64, 65, 66, 68, 69, 67, 8, 9, 7, 60, 58, 59, 54, 52, 53, 55, 56, 57, 78, 76,
        77, 18, 16, 17, 30, 28, 29, 24, 22, 23, 25, 26, 27, 15, 13, 14, 70, 71, 72, 44, 45, 43, 38, 39, 37, 42, 40, 41, 1, 2, 3, 47, 48, 46, 34, 35,
        36, 4, 5, 6, 62, 63, 61, 12, 10, 11, 19, 20, 21 ], [ 76, 77, 78, 79, 80, 81, 44, 45, 43, 37, 38, 39, 68, 69, 67, 60, 58, 59, 54, 52,
        53, 66, 64, 65, 5, 6, 4, 62, 63, 61, 29, 30, 28, 24, 22, 23, 74, 75, 73, 14, 15, 13, 72, 70, 71, 18, 16, 17, 21, 19, 20, 50, 51, 49, 3, 1,
        2, 47, 48, 46, 31, 32, 33, 35, 36, 34, 40, 41, 42, 9, 7, 8, 11, 12, 10, 55, 56, 57, 26, 27, 25 ],
    [ 77, 78, 76, 80, 81, 79, 45, 43, 44, 38, 39, 37, 69, 67, 68, 58, 59, 60, 52, 53, 54, 64, 65, 66, 6, 4, 5, 63, 61, 62, 30, 28, 29,
        22, 23, 24, 75, 73, 74, 15, 13, 14, 70, 71, 72, 16, 17, 18, 19, 20, 21, 51, 49, 50, 1, 2, 3, 48, 46, 47, 32, 33, 31, 36, 34, 35, 41, 42, 40,
        7, 8, 9, 12, 10, 11, 56, 57, 55, 27, 25, 26 ], [ 78, 76, 77, 81, 79, 80, 43, 44, 45, 39, 37, 38, 67, 68, 69, 59, 60, 58, 53, 54, 52,
        65, 66, 64, 4, 5, 6, 61, 62, 63, 28, 29, 30, 23, 24, 22, 73, 74, 75, 13, 14, 15, 71, 72, 70, 17, 18, 16, 20, 21, 19, 49, 50, 51, 2, 3, 1,
        46, 47, 48, 33, 31, 32, 34, 35, 36, 42, 40, 41, 8, 9, 7, 10, 11, 12, 57, 55, 56, 25, 26, 27 ],
    [ 79, 80, 81, 68, 69, 67, 58, 59, 60, 53, 54, 52, 77, 78, 76, 30, 28, 29, 23, 24, 22, 73, 74, 75, 14, 15, 13, 70, 71, 72, 43, 44, 45,
        37, 38, 39, 49, 50, 51, 3, 1, 2, 48, 46, 47, 32, 33, 31, 34, 35, 36, 66, 64, 65, 6, 4, 5, 61, 62, 63, 7, 8, 9, 10, 11, 12, 55, 56, 57, 17,
        18, 16, 21, 19, 20, 26, 27, 25, 41, 42, 40 ], [ 80, 81, 79, 69, 67, 68, 59, 60, 58, 54, 52, 53, 78, 76, 77, 28, 29, 30, 24, 22, 23, 74, 75,
        73, 15, 13, 14, 71, 72, 70, 44, 45, 43, 38, 39, 37, 50, 51, 49, 1, 2, 3, 46, 47, 48, 33, 31, 32, 35, 36, 34, 64, 65, 66, 4, 5, 6,
        62, 63, 61, 8, 9, 7, 11, 12, 10, 56, 57, 55, 18, 16, 17, 19, 20, 21, 27, 25, 26, 42, 40, 41 ],
    [ 81, 79, 80, 67, 68, 69, 60, 58, 59, 52, 53, 54, 76, 77, 78, 29, 30, 28, 22, 23, 24, 75, 73, 74, 13, 14, 15, 72, 70, 71, 45, 43, 44,
        39, 37, 38, 51, 49, 50, 2, 3, 1, 47, 48, 46, 31, 32, 33, 36, 34, 35, 65, 66, 64, 5, 6, 4, 63, 61, 62, 9, 7, 8, 12, 10, 11, 57, 55, 56, 16,
        17, 18, 20, 21, 19, 25, 26, 27, 40, 41, 42 ] ]
