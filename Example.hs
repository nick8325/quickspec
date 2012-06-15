{-# LANGUAGE ScopedTypeVariables #-}

import QuickSpec
import Signature
import Test.QuickCheck
import Data.Typeable
import qualified Heaps as H
import Data.List

bools = [
  vars ["x", "y", "z"] True,
  fun2 "||" (||),
  fun2 "&&" (&&),
  fun1 "not" not, 
  fun0 "True" True,
  fun0 "False" False]

arith :: forall a. (Typeable a, Ord a, Num a, Arbitrary a) => a -> [Sig]
arith _ = [
  vars ["x", "y", "z"] (undefined :: a),
  fun0 "0" (0 :: a),
  fun0 "1" (1 :: a),
  fun2 "+" ((+) :: a -> a -> a),
  fun2 "*" ((*) :: a -> a -> a)]

lists :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> [Sig]
lists _ = [
  vars ["xs", "ys", "zs"] (undefined :: [a]),
  fun1 "length" (length :: [a] -> Int),
  fun1 "reverse" (reverse :: [a] -> [a]),
  fun2 "++" ((++) :: [a] -> [a] -> [a]),
  fun0 "[]" ([] :: [a]),
  fun2 "map" (map :: (a -> a) -> [a] -> [a]),
  fun1 "unit" (return :: a -> [a])]

-- A few more list functions that are helpful for the heaps example.
heapsLists  :: forall a. (Typeable a, Ord a, Arbitrary a) => a -> [Sig]
heapsLists _ = [
  fun1 "sort" (sort :: [a] -> [a]),
  fun2 "insertList" (insert :: a -> [a] -> [a]),
  fun1 "nullList" (null :: [a] -> Bool),
  fun2 "deleteList" (delete :: a -> [a] -> [a]) ]

funs :: forall a. (Typeable a, Ord a, Arbitrary a, CoArbitrary a) => a -> [Sig]
funs _ = [
  vars ["f", "g", "h"] (undefined :: a -> a),
  -- We treat . as a function of two arguments here (blind2)---i.e.,
  -- we do not generate terms of the form (f . g) x.
  blind2 "." (\(f :: a -> a) (g :: a -> a) -> f . g),
  -- Similarly, id is not treated as a function.
  blind0 "id" (id :: a -> a),
  -- Tell QuickSpec how to compare values of function type:
  -- i.e., generate a random argument and apply the function to it.
  observer1 (\(x :: a) (f :: a -> a) -> f x)
  ]

-- Generate a few variables at a particular type.
someVars :: forall a. (Typeable a, Arbitrary a) => a -> Sig
someVars _ = vars ["x", "y", "z"] (undefined :: a)

main = mapM_ quickSpec $ [
  bools,
  arith (undefined :: Int),
  funs (undefined :: Int),
  [someVars 'A',
   silence (funs 'A'),
   silence (arith (undefined :: Int)),
   signature (lists 'A')],
  [someVars 'A',
   silence (lists 'A'),
   silence (heapsLists 'A'),
   signature (H.heaps 'A')]]
