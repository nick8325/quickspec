-- Regular expressions.
{-# LANGUAGE GeneralizedNewtypeDeriving,DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses #-}
import qualified Control.Monad.State as S
import Control.Monad.State hiding (State, state)
import qualified Data.Map as M
import Data.List
import Data.Map(Map)
import Data.Typeable
import QuickSpec
import Test.QuickCheck
import Test.QuickCheck.Random
import Test.QuickCheck.Gen
import Data.Ord
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set
import Debug.Trace

data Sym = A | B deriving (Eq, Ord, Typeable, Show)

instance Arbitrary Sym where
  arbitrary = elements [A, B]

newtype State = State Int deriving (Eq, Ord, Num, Show)

data Regex a = Char a | AnyChar | Epsilon | Zero
             | Concat (Regex a) (Regex a)
             | Choice (Regex a) (Regex a)
             | Deriv a (Regex a)
             | Plus (Regex a) deriving (Typeable, Show)

instance Observe [Sym] Bool (Regex Sym) where
  observe inp r = accepts r inp

instance Arbitrary (Regex Sym) where
  arbitrary = sized arb
    where arb 0 = oneof [fmap Char arbitrary, return AnyChar, return Epsilon, return Zero]
          arb n = oneof [fmap Char arbitrary, return AnyChar, return Epsilon, return Zero,
                         liftM2 Concat arb' arb', liftM2 Choice arb' arb', fmap Plus (arb (n-1))]
            where arb' = arb (n `div` 2)

star r = Choice Epsilon (Plus r)

nub' :: Ord a => [a] -> [a]
nub' = map head . group . sort

charLike :: Maybe a -> Regex a
charLike Nothing = AnyChar
charLike (Just c) = Char c

consume :: (Show a, Ord a) => Regex a -> [a] -> Set [a]
consume (Char x) (y:ys) | x == y = Set.singleton ys
consume AnyChar (_:ys) = Set.singleton ys
consume Epsilon ys = Set.singleton ys
consume (Concat r1 r2) xs =
  consume r1 xs `bind` consume r2
consume (Choice r1 r2) xs =
  consume r1 xs `Set.union` consume r2 xs
consume (Plus r) xs =
  consume r xs `Set.union`
  (consume r xs `bind` \ys ->
   if length xs <= length ys then Set.empty else
   Set.singleton ys `Set.union` consume (Plus r) ys)
consume (Deriv x r) xs =
  --traceShow (x, r, xs) $
  Set.fromList [ ys | ys <- Set.toList (consume r (x:xs)), length ys <= length xs ]
consume _ _ = Set.empty

bind :: (Ord a, Ord b) => Set a -> (a -> Set b) -> Set b
s `bind` f = Set.unions (map f (Set.toList s))

accepts :: (Show a, Ord a) => Regex a -> [a] -> Bool
accepts r xs =
  --traceShow (r, xs) $
  [] `Set.member` consume r xs

main = quickSpec [
  series [
    [con "char" (Char :: Sym -> Regex Sym),
     con "e" (Epsilon :: Regex Sym),
     con "0" (Zero :: Regex Sym),
     con ";" (Concat :: Regex Sym -> Regex Sym -> Regex Sym),
     con "|" (Choice :: Regex Sym -> Regex Sym -> Regex Sym),
     con "*" (star :: Regex Sym -> Regex Sym),
     con "Nothing" (Nothing :: Maybe Sym),
     predicate "/=" ((/=) :: Sym -> Sym -> Bool),
     con "Just" (Just :: Sym -> Maybe Sym)],
    [con "&&" (&&),
     con "||" (||),
     con "True" True,
     con "[]" ([] :: [Sym]),
     con "++" ((++) :: [Sym] -> [Sym] -> [Sym]),
     con "False" False],
    [con "accepts" (accepts :: Regex Sym -> [Sym] -> Bool)],
    [con "deriv" (Deriv :: Sym -> Regex Sym -> Regex Sym)]],
  withMaxTestSize 10,
  withMaxTests 10000,
  monoTypeObserve (Proxy :: Proxy (Regex Sym)),
  monoType (Proxy :: Proxy (Maybe Sym)),
  monoType (Proxy :: Proxy Sym) ]
