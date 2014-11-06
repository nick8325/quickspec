{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances, TypeOperators, ScopedTypeVariables #-}
import Prelude hiding ((/))
import qualified Prelude
import Data.Ratio
import Control.Monad
import Control.Monad.IO.Class
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
instance Arbitrary It where arbitrary = liftM2 (curry It) it arbitrary

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
  One | Star | Inverse |
  -- Functionals
  Id | Compose | Inversion | L1 | R1 | L2 | R2 | Apply | C | T | J | ConjJ
  deriving (Enum, Bounded, Show)
instance Pretty Const where
  pretty = text . prettyShow

instance ConLike Const where
  toConstant One       =  constant "1"   (ident :: It)
  toConstant Star      =  constant "*"   (op :: It -> It -> It)
  toConstant Inverse   = (constant "^-1" (inv :: It -> It)) { conStyle = Postfix }
  toConstant Id        =  constant "id"  (ident :: ItFun)
  toConstant Compose   =  constant "."   (op    :: ItFun -> ItFun -> ItFun)
  toConstant Inversion = (constant "^-1" (inv   :: ItFun -> ItFun)) { conStyle = Postfix }
  toConstant L1        = (constant "L"   (l :: It -> ItFun))     { conStyle = Uncurried }
  toConstant R1        = (constant "R"   (r :: It -> ItFun))     { conStyle = Uncurried }
  toConstant L2        = (constant "L"  (l2 :: It -> It -> ItFun))    { conStyle = Uncurried }
  toConstant R2        = (constant "R"  (r2 :: It -> It -> ItFun))    { conStyle = Uncurried }
  toConstant Apply     =  constant "@"   (flip apply :: It -> ItFun -> It)
  toConstant C         = (constant "C"   (c :: It -> It -> ItFun))     { conStyle = Uncurried }
  toConstant T         = (constant "T"   (t :: It -> ItFun))     { conStyle = Uncurried }
  toConstant J         = (constant "J"   (j :: ItFun))
  toConstant ConjJ     = (constant "^J"  (jconj :: ItFun -> ItFun)) { conStyle = Postfix }

sig1 =
  signature {
    constants = map toConstant [One, Star, Inverse],
    maxTests = Just 5,
    instances = [
      baseType (undefined :: It) ]}
  where

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
    maxTests = Just 5,
    constants = map toConstant [Id, Compose, Inversion],
    instances = [
      names (NamesFor ["f", "g", "h"] :: NamesFor ItFun),
      inst (Sub Dict :: () :- Arbitrary ItFun),
      makeInstance (\() -> observe obsItFun) ]}

sig3 =
  signature {
    constants = map toConstant [L1, R1, L2, R2, Apply, C, T, J, ConjJ],
    --QuickSpec.simplify = Just Main.simplify,
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
    toTerm = mapTerm toConstant id
    fromTerm = mapTerm (fromConstant sig) id
simplify sig prop = prop

simplifyTerm :: Tm Const Variable -> Tm Const Variable
simplifyTerm (Fun Apply [x, t]) | groundFuns t = simplifyTerm (apply (toFun t) x)
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
{-
main = do
  thy1 <- quickSpec sig1
  thy2 <- quickSpec sig2
  let sig = thy1 `mappend` thy2 `mappend` sig3
  quickSpec sig
-}

main = quickSpec sig1
