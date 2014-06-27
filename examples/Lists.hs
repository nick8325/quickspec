{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickSpec hiding (lists)
import Test.QuickCheck
import Data.Typeable

lists :: forall a. (Typeable a, Ord a, Arbitrary a, CoArbitrary a) =>
         a -> [Sig]
lists a = [
  prelude (undefined :: a) `without` ["++"],
  funs (undefined :: a),

  "unit"    `fun1` (return  :: a -> [a]),
  -- Don't take ++ from the prelude because we want to see laws about it
  "++"      `fun2` ((++)    :: [a] -> [a] -> [a]),
  "length"  `fun1` (length  :: [a] -> Int),
  "reverse" `fun1` (reverse :: [a] -> [a]),
  "map"     `fun2` (map     :: (a -> a) -> [a] -> [a])
  ]

main = quickSpec (lists (undefined :: A))
