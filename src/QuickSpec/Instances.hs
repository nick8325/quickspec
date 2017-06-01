{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}
module QuickSpec.Instances where

import QuickSpec.FindInstance
import QuickSpec.Type
import Test.QuickCheck
import Data.Constraint
import Data.Proxy

baseInstances :: Instances
baseInstances =
  mconcat [
    -- Generate tuple values (pairs and () are built into findInstance)
    inst $ \(x :: A) (y :: B) (z :: C) -> (x, y, z),
    inst $ \(x :: A) (y :: B) (z :: C) (w :: D) -> (x, y, z, w),
    inst $ \(x :: A) (y :: B) (z :: C) (w :: D) (v :: E) -> (x, y, z, w, v),
    -- Split conjunctions of typeclasses into individuals
    inst $ \() -> Dict :: Dict (),
    inst $ \(Dict :: Dict ClsA) (Dict :: Dict ClsB) -> Dict :: Dict (ClsA, ClsB),
    inst $ \(Dict :: Dict ClsA) (Dict :: Dict ClsB) (Dict :: Dict ClsC) -> Dict :: Dict (ClsA, ClsB, ClsC),
    inst $ \(Dict :: Dict ClsA) (Dict :: Dict ClsB) (Dict :: Dict ClsC) (Dict :: Dict ClsD) -> Dict :: Dict (ClsA, ClsB, ClsC, ClsD),
    inst $ \(Dict :: Dict ClsA) (Dict :: Dict ClsB) (Dict :: Dict ClsC) (Dict :: Dict ClsD) (Dict :: Dict ClsE) -> Dict :: Dict (ClsA, ClsB, ClsC, ClsD, ClsE),
    -- Derive typeclass instances using (:-)
    inst $ \(Dict :: Dict ClsA) (Sub Dict :: ClsA :- ClsB) -> Dict :: Dict ClsB,
    -- Standard names
    inst $ \(Names names :: Names A) ->
      Names (map (++ "s") names) :: Names [A],
    inst (Names ["p", "q", "r"] :: Names (A -> Bool)),
    inst (Names ["f", "g", "h"] :: Names (A -> B)),
    inst (Names ["x", "y", "z"] :: Names A),
    -- Standard instances
    baseType (Proxy :: Proxy ()),
    baseType (Proxy :: Proxy Int),
    baseType (Proxy :: Proxy Integer),
    baseType (Proxy :: Proxy Bool),
    baseType (Proxy :: Proxy Char),
    inst (Sub Dict :: () :- CoArbitrary ()),
    inst (Sub Dict :: () :- CoArbitrary Int),
    inst (Sub Dict :: () :- CoArbitrary Integer),
    inst (Sub Dict :: () :- CoArbitrary Bool),
    inst (Sub Dict :: () :- CoArbitrary Char),
    inst (Sub Dict :: Ord A :- Eq A),
    -- From Arbitrary to Gen
    inst $ \(Dict :: Dict (Arbitrary A)) -> arbitrary :: Gen A,
    inst $ \(dict :: Dict ClsA) -> return dict :: Gen (Dict ClsA)]

baseType :: forall proxy a. (Ord a, Arbitrary a, Typeable a) => proxy a -> Instances
baseType _ =
  mconcat [
    inst (Dict :: Dict (Ord a)),
    inst (Dict :: Dict (Arbitrary a))]

newtype Names a = Names { getNames :: [String] }

names :: Instances -> Type -> [String]
names insts ty =
  case findInstance insts (skolemiseTypeVars ty) of
    (x:_) -> ofValue getNames x
