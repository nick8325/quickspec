{-# LANGUAGE ScopedTypeVariables, TypeOperators, GADTs, FlexibleInstances #-}
module QuickSpec.Haskell where

import QuickSpec.Haskell.Resolve
import QuickSpec.Type
import Test.QuickCheck
import Data.Constraint
import Data.Proxy
import qualified Twee.Base as B
import QuickSpec.Term
import Data.Functor.Identity
import Data.Maybe
import Data.MemoUgly
import Test.QuickCheck.Gen
import Test.QuickCheck.Gen.Unsafe

baseInstances :: Instances
baseInstances =
  mconcat [
    -- Generate tuple values (pairs and () are built into findInstance)
    inst $ \(x :: A) (y :: B) (z :: C) -> (x, y, z),
    inst $ \(x :: A) (y :: B) (z :: C) (w :: D) -> (x, y, z, w),
    inst $ \(x :: A) (y :: B) (z :: C) (w :: D) (v :: E) -> (x, y, z, w, v),
    -- Split conjunctions of typeclasses into individuals
    inst $ \() -> Dict :: Dict (),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) -> Dict :: Dict (ClassA, ClassB),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) (Dict :: Dict ClassC) -> Dict :: Dict (ClassA, ClassB, ClassC),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) (Dict :: Dict ClassC) (Dict :: Dict ClassD) -> Dict :: Dict (ClassA, ClassB, ClassC, ClassD),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) (Dict :: Dict ClassC) (Dict :: Dict ClassD) (Dict :: Dict ClassE) -> Dict :: Dict (ClassA, ClassB, ClassC, ClassD, ClassE),
    -- Derive typeclass instances using (:-)
    -- N.B. flip is there to resolve (:-) first to reduce backtracking
    inst $ flip $ \(Dict :: Dict ClassA) (Sub Dict :: ClassA :- ClassB) -> Dict :: Dict ClassB,
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
    inst (Sub Dict :: Ord A :- Ord [A]),
    inst (Sub Dict :: Arbitrary A :- Arbitrary [A]),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary [A]),
    inst (Sub Dict :: Ord A :- Eq A),
    -- From Arbitrary to Gen
    inst $ \(Dict :: Dict (Arbitrary A)) -> arbitrary :: Gen A,
    inst $ \(dict :: Dict ClassA) -> return dict :: Gen (Dict ClassA),
    -- From Dict to OrdDict
    inst (OrdDict :: Dict (Ord A) -> OrdDict A)]

newtype OrdDict a = OrdDict (Dict (Ord a)) deriving Typeable

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

arbitraryVal :: Instances -> Gen (Var -> Value Maybe)
arbitraryVal insts =
  MkGen $ \g n -> memo $ \(V ty x) ->
    case typ ty of
      Nothing ->
        fromJust $ cast ty (toValue (Nothing :: Maybe A))
      Just gen ->
        forValue gen $ \gen ->
          Just (unGen (coarbitrary x gen) g n)
  where
    typ :: Type -> Maybe (Value Gen)
    typ = memo $ \ty ->
      case findInstance insts ty of
        [] -> Nothing
        (gen:_) ->
          Just (mapValue (coarbitrary ty) gen)

ordyVal :: Instances -> Value Identity -> Maybe (Value Ordy)
ordyVal insts =
  \x ->
    case ordyTy (typ x) of
      Nothing -> Nothing
      Just f -> Just (f x)
  where
    ordyTy :: Type -> Maybe (Value Identity -> Value Ordy)
    ordyTy = memo $ \ty ->
      case findInstance insts ty :: [Value OrdDict] of
        [] -> Nothing
        (val:_) ->
          case unwrap val of
            OrdDict Dict `In` w ->
              Just $ \val ->
                wrap w (Ordy (runIdentity (reunwrap w val)))

data Ordy a where Ordy :: Ord a => a -> Ordy a
instance Eq (Value Ordy) where x == y = compare x y == EQ

instance Ord (Value Ordy) where
  compare x y =
    compare (typ x) (typ y) `mappend`
    case unwrap x of
      Ordy xv `In` w ->
        let Ordy yv = reunwrap w y in
        compare xv yv

eval :: Instances -> (f -> Value Maybe) -> (Var -> Value Maybe) -> Term f -> Either (Value Ordy) (Term f)
eval insts ev env t =
  case unwrap (evaluateTerm ev env t) of
    Nothing `In` _ -> Right t
    Just val `In` w ->
      case ordyVal insts (wrap w (Identity val)) of
        Nothing -> Right t
        Just ordy -> Left ordy
