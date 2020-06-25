{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}

module AutoGeneralized where

import QuickSpec
import Test.QuickCheck


data Foo a b
  = A a
  | B b
  deriving (Eq, Ord, Show)

instance Arbitrary (Foo () ()) where
  arbitrary = elements
    [ A ()
    , B ()
    ]


main = quickSpec
  [ con "A" $ A @() @()
  , monoType $ Proxy @(Foo () ())
  , withAutoGeneralizedTypes False
  ]

