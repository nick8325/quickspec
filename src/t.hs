{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, DeriveDataTypeable, ScopedTypeVariables, TypeOperators #-}
import Data.Ratio
import QuickSpec
import Test.QuickCheck
import Control.Monad
import Prelude hiding ((/), (\\))
import qualified Prelude
import Data.Typeable hiding (typeOf)
import Octonions
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Base hiding (text, (<>), compose, nest, ($$))
import QuickSpec.Eval
import QuickSpec.Test
import QuickSpec.Prop
import QuickSpec.Signature hiding (sig)
import qualified QuickSpec.Signature as S
import Data.Monoid hiding ((<>))
import PrettyPrinting
import Data.Constraint hiding ((\\))
import qualified Ords
import Zipper
import Process hiding ( Nil )
import qualified Process as P
import Data.List ( delete )

(\\), (/) :: It -> It -> It
a / b = a * recip b
b \\ a = recip b * a

l, r, l1, r1, t :: It -> ItFun
l x = ItFun (\y -> x * y)
r x = ItFun (\y -> y * x)
l1 x = ItFun (\y -> x \\ y)
r1 x = ItFun (\y -> y / x)
t x = r x `compose` l1 x

compose :: ItFun -> ItFun -> ItFun
compose (ItFun f) (ItFun g) = ItFun (f . g)

listsSig =
  signature {
    constants = [
      constant "rev" (reverse :: [A] -> [A]),
      constant "app" ((++) :: [A] -> [A] -> [A]),
      constant "[]" ([] :: [A]),
      constant "map" (map :: (A -> B) -> [A] -> [B]) ]}

constSig =
  mconcat [
    signature {
       constants = [
          constant "const" ((\x y -> [const x y]) :: A -> B -> [A]),
          constant "asTypeOf" ((\x y -> [asTypeOf x y]) :: A -> A -> [A]) ] }]

boolSig =
  mconcat [
     signature {
        constants = [
           constant "True" True,
           constant "False" False,
           constant "||" (||),
           constant "&&" (&&),
           constant "not" not ]}]

octSig =
  signature {
    constants = [
       constant "1" (1 :: It),
       constant "*" ((*) :: It -> It -> It),
       --  constant "/" ((/) :: It -> It -> It),
       --  constant "\\" ((\\) :: It -> It -> It),
       constant "id" (ItFun id),
       (constant "l" l)   { conStyle = Uncurried },
       (constant "r" r)   { conStyle = Uncurried },
       (constant "l1" l1) { conStyle = Uncurried },
       (constant "r1" r1) { conStyle = Uncurried },
       (constant "t" t)   { conStyle = Uncurried },
       constant "." compose ],
    background = octBackground,
    instances = [
      baseType (undefined :: ItFun),
      baseType (undefined :: It)]}
  where
    star = constant "*" ((*) :: It -> It -> It)
    lc = constant "l" l
    rc = constant "r" r
    dot = constant "." compose
    bi = Predicate "bi" (typeOf (undefined :: It -> It -> It -> Bool))
    x  = Var $ Variable 0 (typeOf (undefined :: It))
    y  = Var $ Variable 1 (typeOf (undefined :: It))
    a  = Var $ Variable 3 (typeOf (undefined :: It))
    b  = Var $ Variable 4 (typeOf (undefined :: It))
    c  = Var $ Variable 5 (typeOf (undefined :: It))
    octBackground = [
      [] :=>: bi :@: [x, y, x],
      [] :=>: bi :@: [x, y, y],
      [bi :@: [x, y, a],
       bi :@: [x, y, b]] :=>: bi :@: [x, y, Fun star [a, b]],
      [bi :@: [x, y, a],
       bi :@: [x, y, b],
       bi :@: [x, y, c]] :=>: Fun star [a, Fun star [b, c]] :=: Fun star [Fun star [a, b], c]]

data Table9Point1 = I | A | B | C | D deriving (Eq, Ord, Show, Typeable)

instance Arbitrary Table9Point1 where
  arbitrary = elements [I, A, B, C, D]

instance CoArbitrary Table9Point1 where
  coarbitrary = coarbitraryShow

times :: Table9Point1 -> Table9Point1 -> Table9Point1
times I I = I
times I A = A
times I B = B
times I C = C
times I D = D
times A I = A
times A A = A
times A B = B
times A C = D
times A D = D
times B I = B
times B A = B
times B B = D
times B C = A
times B D = A
times C I = C
times C A = D
times C B = A
times C C = B
times C D = B
times D I = D
times D A = D
times D B = A
times D C = B
times D D = B

table9point1 =
  signature {
      constants = [
        constant "times" times,
        constant "i" I,
        constant "a" A,
        constant "b" B,
        constant "c" C,
        constant "d" D ],
      instances = [
        baseType (undefined :: Table9Point1)]}

arithSig =
  signature {
    constants = [
       constant "0" (0 :: Int),
       constant "1" (1 :: Int),
       constant "+" ((+) :: Int -> Int -> Int),
       constant "*" ((*) :: Int -> Int -> Int) ]}

prettyBackgroundSig =
  signature {
    constants = [
       constant "[]" ([] :: [A]),
       constant "++" ((++) :: [A] -> [A] -> [A]),
       constant "0" (0 :: Int),
       constant "+" ((+) :: Int -> Int -> Int),
       constant "length" (length :: [A] -> Int) ]}

prettySig =
  signature {
    constants = [
       constant "text" (text :: [A] -> Layout A),
       constant "nest" (nest :: Int -> Layout A -> Layout A),
       constant "$$" (($$) :: Layout A -> Layout A -> Layout A),
       constant "<>" ((<>) :: Layout A -> Layout A -> Layout A) ],
    instances = [
      inst (Sub Dict :: Ord A         :- Ord       (Layout A)),
      inst (Sub Dict :: Arbitrary A   :- Arbitrary (Layout A)),
      inst (Sub Dict :: CoArbitrary A :- CoArbitrary (Layout A)) ],
    defaultTo = [typeOf (undefined :: Bool)] }

ordSig =
  signature {
    constants = [
       constant "0" Ords.Zero,
       (constant "s" Ords.Succ) { conStyle = Uncurried },
       constant "+" Ords.plus,
       constant "*" Ords.times ],
    instances = [
      baseType (undefined :: Ords.Ordinal) ]}

zipperSig =
  signature {
    constants = [
       constant "nothing" (Nothing :: Maybe A),
       constant "nil" Nil,
       constant "cons" Cons,
       constant "change" change,
       constant "up" up,
       constant "upLeft" upLeft,
       constant "upRight" upRight,
       constant "left" left,
       constant "right" right,
       constant "fromZipper" fromZipper,
       constant "toZipper" toZipper ],
    instances = [
      baseType (undefined :: Zipper),
      baseType (undefined :: Tree) ]}

newtype P_ = P_ P
 deriving ( Eq, Ord, Arbitrary, CoArbitrary, Typeable )

newtype Name_ = Name_ [P.Name]
 deriving ( Eq, Ord, CoArbitrary, Typeable )

instance Arbitrary Name_ where
  arbitrary =
    do a <- arbitrary
       b <- arbitrary `suchThat` (/=a)
       return (Name_ [a,b])

processSig =
  signature
  { constants =
    -- Event
    [ -- con "in"  P.In
    -- , con "out" Out
    -- , con "tau" Tau
    
    -- Restricted processes
      con "/"    (\(P_ p) a -> p // a)
    
    -- Restricted names
    , con "#"    (\(Name_ as) b -> head (filter (/=b) as))
    
    -- P
    , con "0"    P.Nil
    -- , con "."    Act
    , con "?"    (Act . P.In)
    , con "!"    (Act . Out)
    , con "tau"  (Act Tau)
    , con "+"    (:+:)
    , con "|"    (:|:)
    , (con "*"   Star){ conStyle = Postfix }
    , con "new"  New
    ]
    
  , instances =
    [ baseTypeNames ["a","b","c"] (undefined :: P.Name)
    , baseTypeNames ["c"] (undefined :: Name_)
    -- , baseTypeNames ["e"]         (undefined :: P.Event)
    , baseTypeNames ["p","q","r"] (undefined :: P)
    , baseTypeNames ["r"] (undefined :: P_)
    ]
    
  , defaultTo = [typeOf (undefined :: Bool)]
  }
 where
  con op f = constant op f

main = quickSpec processSig
--main = quickSpecWithBackground processBackgroundSig processSig
--main = quickSpec octSig
