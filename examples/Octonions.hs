{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances, TypeOperators, ScopedTypeVariables #-}
import Prelude hiding ((/))
import qualified Prelude
import Data.Ratio
import Control.Monad
import Test.QuickCheck hiding (Result)
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Data.Ord
import Data.Monoid
import Data.List hiding ((\\))
import QuickSpec hiding (compose, (\\), Result, apply)

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

data Ext a = Normal a | Weird a deriving (Eq, Ord, Typeable, Show)

instance Arbitrary a => Arbitrary (Ext a) where
  arbitrary = oneof [fmap Normal arbitrary, fmap Weird arbitrary]
instance CoArbitrary a => CoArbitrary (Ext a) where
  coarbitrary (Normal x) = variant (0 :: Int) . coarbitrary x
  coarbitrary (Weird x)  = variant (1 :: Int) . coarbitrary x
instance Group a => Group (Ext a) where
  ident = Normal ident
  inv (Normal x) = Normal (inv x)
  inv (Weird x)  = Weird  x
  op (Normal x) (Normal y) = Normal (op x y)
  op (Weird x)  (Normal y) = Weird (op x (inv y))
  op (Normal x) (Weird y)  = Weird (op y x)
  op (Weird x)  (Weird y)  = Normal (op (inv y) x)

newtype It = It (Octonion, Ext Perms) deriving (Eq, Ord, Typeable, CoArbitrary, Group, Show)
newtype ItFun = ItFun (It -> It) deriving (Arbitrary, CoArbitrary, Typeable)
apply :: ItFun -> It -> It
apply (ItFun f) x = f x

instance Arbitrary It where arbitrary = liftM2 (curry It) it arbitrary

(\\), (/) :: It -> It -> It
a / b = a `op` inv b
b \\ a = inv b `op` a

l, r, l', r', t :: It -> ItFun
l x = ItFun (\y -> x `op` y)
r x = ItFun (\y -> y `op` x)
l' x = ItFun (\y -> x \\ y)
r' x = ItFun (\y -> y / x)
t x = r x `compose` l' x
t' x = l x `compose` r' x

l2, r2, l2', r2', c :: It -> It -> ItFun
l2 x y = l x `compose` l y `compose` l' (y `op` x)
r2 x y = r x `compose` r y `compose` r' (x `op` y)
l2' x y = l (y `op` x) `compose` l' y `compose` l' x
r2' x y = r (x `op` y) `compose` r' y `compose` r' x
c x y = r x `compose` l y `compose` r (inv x) `compose` l (inv y)
j :: ItFun
j = ItFun inv

jconj :: ItFun -> ItFun
jconj f = j `compose` f `compose` j

infixr `compose`
compose :: ItFun -> ItFun -> ItFun
compose (ItFun f) (ItFun g) = ItFun (f . g)

obsItFun :: ItFun -> Gen It
obsItFun (ItFun f) = fmap f arbitrary

sig1 =
  signature {
    constants = [
      constant "1" (ident :: It),
      star,
      (constant "^-1" (inv :: It -> It)) { conStyle = Postfix } ],
    maxTests = Just 5,
    extraPruner = Just None,
    instances = [
      baseType (undefined :: It) ]}
  where
    star = constant "*" (op :: It -> It -> It)

diassociativity :: [Prop]
diassociativity = map (parseProp (constants sig1 ++ [bi])) background
  where
    bi = constant "bi" (undefined :: It -> It -> It -> Bool)
    background = [
      "bi(X, Y, Z)",
      "bi(X, Y, Y)",
      "bi(X, Y, A) & bi(X, Y, B) => bi(X, Y, *(A, B))",
      "bi(X, Y, A) & bi(X, Y, B) & bi(X, Y, C) => *(A, *(B, C)) = *(*(A, B), C)"]

sig2 =
  signature {
    extraPruner = Just None,
    maxTests = Just 5,
    constants = [
      constant "id" (ItFun id),
      constant "." compose ],
    instances = [
      names (NamesFor ["f", "g", "h"] :: NamesFor ItFun),
      inst (Sub Dict :: () :- Arbitrary ItFun),
      makeInstance (\() -> observe obsItFun) ]}

sig3 =
  signature {
    constants = [
      (constant "L" l)   { conStyle = Uncurried },
      (constant "R" r)   { conStyle = Uncurried },
      --(constant "L^-1" l') { conStyle = Uncurried },
      --(constant "R^-1" r') { conStyle = Uncurried },
      (constant "L2" l2)  { conStyle = Uncurried },
      (constant "R2" r2)  { conStyle = Uncurried },
      --(constant "L2^-1" l2')  { conStyle = Uncurried },
      --(constant "R2^-1" r2')  { conStyle = Uncurried },
      constant "@" (flip apply),
      --(constant "" Result) { conStyle = Curried },
      (constant "C" c)   { conStyle = Uncurried },
      (constant "T" t)   { conStyle = Uncurried },
      (constant "J" j),
      (constant "^J" jconj) { conStyle = Postfix }],
      --(constant "T^-1" t')   { conStyle = Uncurried }],
    maxTests = Just 5}
    --instances = [baseType (undefined :: Result)],
    --background = background,

main = do
  thy1 <- quickSpec sig1
  thy2 <- quickSpec sig2
  quickSpec (thy1 `mappend` thy2 `mappend` sig3)
