{-# LANGUAGE ScopedTypeVariables, TypeOperators, GADTs, FlexibleInstances, FlexibleContexts #-}
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
import Control.Monad
import System.Random

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
    inst (OrdDict :: Dict (Ord A) -> OrdDict A),
    -- Observe
    inst (\(Dict :: Dict (Ord A)) -> Observe (return id) :: Observe A A),
    inst (\(Observe obsm :: Observe B C) (xm :: Gen A) ->
      Observe (do {x <- xm; obs <- obsm; return (\f -> obs (f x))}) :: Observe (A -> B) C),
    inst (\(obs :: Observe A B) -> Observe1 (toValue obs))]

data Observe a b where
  Observe :: Ord b => Gen (a -> b) -> Observe a b
  deriving Typeable
data Observe1 a = Observe1 (Value (Observe a)) deriving Typeable

-- data SomeObserve a = forall args res. (Ord res, Arbitrary args) => SomeObserve (a -> args -> res) deriving Typeable

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

arbitraryVal :: Instances -> Gen (Var -> Value Maybe, Value Identity -> Maybe TestResult)
arbitraryVal insts =
  MkGen $ \g n ->
    let (g1, g2) = split g in
    (memo $ \(V ty x) ->
       case typ ty of
         Nothing ->
           fromJust $ cast ty (toValue (Nothing :: Maybe A))
         Just gen ->
           forValue gen $ \gen ->
             Just (unGen (coarbitrary x gen) g1 n),
     unGen (ordyVal insts) g2 n) 
  where
    typ :: Type -> Maybe (Value Gen)
    typ = memo $ \ty ->
      case findInstance insts ty of
        [] -> Nothing
        (gen:_) ->
          Just (mapValue (coarbitrary ty) gen)

ordyVal :: Instances -> Gen (Value Identity -> Maybe TestResult)
ordyVal insts =
  MkGen $ \g n -> \x ->
    case ordyTy (typ x) of
      Nothing -> Nothing
      Just f -> Just (TestResult (typ x) (unGen f g n x))
  where
    ordyTy :: Type -> Maybe (Gen (Value Identity -> Value Ordy))
    ordyTy = memo $ \ty ->
      case findInstance insts ty :: [Value Observe1] of
        [] -> Nothing
        (val:_) ->
          case unwrap val of
            Observe1 val `In` w1 ->
              case unwrap val of
                Observe obs `In` w2 ->
                  Just $
                    MkGen $ \g n ->
                      let observe = unGen obs g n in
                      \x -> wrap w2 (Ordy (observe (runIdentity (reunwrap w1 x))))

data TestResult = TestResult Type (Value Ordy) deriving (Eq, Ord, Show)

data Ordy a where Ordy :: Ord a => a -> Ordy a
instance Eq (Value Ordy) where x == y = compare x y == EQ

instance Ord (Value Ordy) where
  compare x y =
    compare (typ x) (typ y) `mappend`
    case unwrap x of
      Ordy xv `In` w ->
        let Ordy yv = reunwrap w y in
        compare xv yv

evalHaskell :: Eval f (Value Maybe) => Instances -> (Var -> Value Maybe, Value Identity -> Maybe TestResult) -> Term f -> Either TestResult (Term f)
evalHaskell insts (env, obs) t =
  case unwrap (eval env t) of
    Nothing `In` _ -> Right t
    Just val `In` w ->
      case obs (wrap w (Identity val)) of
        Nothing -> Right t
        Just ordy -> Left ordy
