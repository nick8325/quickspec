module DecisionTrees where

import QuickSpec
import Test.QuickCheck
import Data.List
import Data.Ord
import qualified Data.Set as Set
import Data.Set(Set)

data Tree d a =
    Leaf a
  | Choice d (Tree d a) (Tree d a)
  deriving Show

instance (Arbitrary a, Arbitrary d) => Arbitrary (Tree d a) where
  arbitrary = sized arb
    where
      arb 0 = Leaf <$> arbitrary
      arb n = Choice <$> arbitrary <*> arb' <*> arb'
        where
          arb' = arb (n `div` 2)

class Ord d => Decision d where
  conj :: [d] -> d
  neg :: d -> d

disj :: Decision d => [d] -> d
disj = neg . conj . map neg

true, false :: Decision d => d
true = conj []
false = neg true

flatten :: Decision d => Tree d a -> [(d, a)]
flatten t = flat true t []
  where
    flat d (Leaf x) xs
      | d == false = xs
      | otherwise = (d, x):xs
    flat d (Choice d' t u) xs =
      flat (conj [d, d']) t $
      flat (conj [d, neg d']) u xs

instance (Decision d, Ord a) => Eq (Tree d a) where
  t == u = compare t u == EQ

instance (Decision d, Ord a) => Ord (Tree d a) where
  compare = comparing (sort . flatten)

class Finite a where
  univ :: Set a

newtype Five = Five Int
  deriving (Eq, Ord, Show)

instance Arbitrary Five where
  arbitrary = elements (Set.toList univ)

instance Finite Five where
  univ = Set.fromList (map Five [1..5])

instance (Finite a, Ord a) => Decision (Set a) where
  conj [] = univ
  conj (x:xs) = x `Set.intersection` conj xs
  neg x = univ Set.\\ x

main =
  quickSpec [
    withMaxTermSize 9,
    monoTypeWithVars ["t", "u", "v"] (Proxy :: Proxy (Tree (Set Five) Int)),
    monoTypeWithVars ["p", "q", "r"] (Proxy :: Proxy (Set Five)),
    series
      [[con "true" (true :: Set Five),
        con "false" (false :: Set Five),
        --con "neg" (neg :: Set Five -> Set Five),
        con "&" (\x y -> conj [x, y] :: Set Five),
        predicate "isSubsetOf" (\x y -> conj [x, y] == (x :: Set Five))],
        --con "|" (\x y -> disj [x, y] :: Set Five)
       [--con "Leaf" (Leaf :: Int -> Tree (Set Five) Int),
        con "Choice" (Choice :: Set Five -> Tree (Set Five) Int -> Tree (Set Five) Int -> Tree (Set Five) Int)]]]
