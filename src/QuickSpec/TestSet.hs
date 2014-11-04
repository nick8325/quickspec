{-# LANGUAGE FunctionalDependencies #-}
module QuickSpec.TestSet where

import QuickSpec.Base
import QuickSpec.Type
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Constraint
import Control.Monad

data TestSet t =
  TestSet {
    makeType :: Type -> Maybe (Value (TypedTestSet t)),
    testSet :: Map Type (Value (TypedTestSet t))
    }

data TypedTestSet t a =
  TypedTestSet {
    makeTerm :: t -> Maybe [a],
    dict :: Dict (Ord a),
    testResults :: TestResults t a }

data TestResults t a = TestCase (Map a (TestResults t a)) | Singleton (Tested t a)

data Tested t a =
  Tested {
    testedTerm  :: t,
    tests :: [a] }

emptyTestSet :: (Type -> Maybe (Value (TypedTestSet t))) -> TestSet t
emptyTestSet makeType = TestSet makeType Map.empty

emptyTypedTestSet :: Ord a => (t -> Maybe [a]) -> TypedTestSet t a
emptyTypedTestSet makeTerm = TypedTestSet makeTerm Dict (TestCase Map.empty)

data Result t = New (TestSet t) | Old t

findTestSet :: Typed t => t -> TestSet t -> Maybe (Value (TypedTestSet t))
findTestSet x ts =
  Map.lookup (typ x) (testSet ts) `mplus`
  makeType ts (typ x)

insert :: Typed t => t -> TestSet t -> Maybe (Result t)
insert x ts = do
  tts `In` w <- fmap unwrap (findTestSet x ts)
  tt <- fmap (Tested x) (makeTerm tts x)
  return $
    case insert1 tt tts of
      New1 tts ->
        New ts { testSet = Map.insert (typ x) (wrap w tts) (testSet ts) }
      Old1 t ->
        Old t

data Result1 t a = New1 (TypedTestSet t a) | Old1 t

insert1 :: Typed t => Tested t a -> TypedTestSet t a -> Result1 t a
insert1 x ts =
  case dict ts of
    Dict -> aux k (testedTerm x) (tests x) (testResults ts)
  where
    k res = ts { testResults = res }
    aux _ _ [] (Singleton (Tested y [])) = Old1 y
    aux k x ts (Singleton (Tested y (t':ts'))) =
      aux k x ts (TestCase (Map.singleton t' (Singleton (Tested y ts'))))
    aux k x (t:ts) (TestCase res) =
      case Map.lookup t res of
        Nothing -> New1 (k (TestCase (Map.insert t (Singleton (Tested x ts)) res)))
        Just res' ->
          let k' r = k (TestCase (Map.insert t r res)) in
          aux k' x ts res'
