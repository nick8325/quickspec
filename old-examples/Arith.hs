-- Natural number functions.

{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickSpec hiding (arith)
import Test.QuickCheck
import Data.Typeable

arith :: forall a. (Typeable a, Ord a, Num a, Arbitrary a) => a -> [Sig]
arith _ = [
  ["x", "y", "z"] `vars` (undefined :: a),

  "0" `fun0` (0   :: a),
  "1" `fun0` (1   :: a),
  "+" `fun2` ((+) :: a -> a -> a),
  "*" `fun2` ((*) :: a -> a -> a)]

main = quickSpec (arith (undefined :: Int))
