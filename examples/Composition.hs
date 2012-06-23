{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickSpec
import Test.QuickCheck
import Data.Typeable

composition :: forall a. (Typeable a, Ord a, Arbitrary a, CoArbitrary a) =>
               a -> [Sig]
composition _ = [
  vars ["f", "g", "h"] (undefined :: a -> a),

  -- We treat . as a function of two arguments here (blind2)---i.e.,
  -- we do not generate terms of the form (f . g) x.
  blind2 "."   ((.) :: (a -> a) -> (a -> a) -> (a -> a)),

  -- Similarly, id is not treated as a function.
  blind0 "id"  (id  :: a -> a),

  -- Tell QuickSpec how to compare values of function type:
  -- i.e., generate a random argument and apply the function to it.
  observer2 $ \x (f :: a -> a) -> f x
  ]

main = quickSpec (composition (undefined :: A))
