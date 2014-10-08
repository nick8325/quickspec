module Test.QuickSpec.TestSet where

import Test.QuickSpec.Term
import Test.QuickSpec.Type
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Constraint
import Control.Monad

data TestSet =
  TestSet {
    makeType :: Type -> Maybe (Value TestedTerms),
    testSet :: Map (Poly Type) (Value TestedTerms)
    }

data TestedTerms a =
  TestedTerms {
    makeTerm :: Term -> Maybe [a],
    dict :: Dict (Ord a),
    testResults :: TestResults a }

data TestResults a = TestCase (Map a (TestResults a)) | Singleton (TestedTerm a)

data TestedTerm a =
  TestedTerm {
    term  :: Term,
    tests :: [a] }

emptyTestSet :: (Type -> Maybe (Value TestedTerms)) -> TestSet
emptyTestSet makeType = TestSet makeType Map.empty

emptyTestedTerms :: Ord a => (Term -> Maybe [a]) -> TestedTerms a
emptyTestedTerms makeTerm = TestedTerms makeTerm Dict (TestCase Map.empty)

data Result = New TestSet | Old Term

findTestSet :: Poly Term -> TestSet -> Maybe (Value TestedTerms)
findTestSet x ts =
  Map.lookup (polyTyp x) (testSet ts) `mplus`
  makeType ts (typ x)

insert :: Poly Term -> TestSet -> Maybe Result
insert x ts = do
  tts `In` w <- fmap unwrap (findTestSet x ts)
  tt <- fmap (TestedTerm (unPoly x)) (makeTerm tts (unPoly x))
  return $
    case insert1 tt tts of
      New1 tts ->
        New ts { testSet = Map.insert (polyTyp x) (wrap w tts) (testSet ts) }
      Old1 t ->
        Old t

data Result1 a = New1 (TestedTerms a) | Old1 Term

insert1 :: TestedTerm a -> TestedTerms a -> Result1 a
insert1 x ts =
  case dict ts of
    Dict -> aux k (term x) (tests x) (testResults ts)
  where
    k res = ts { testResults = res }
    aux :: Ord a => (TestResults a -> TestedTerms a) -> Term -> [a] -> TestResults a -> Result1 a
    aux _ _ [] (Singleton (TestedTerm y [])) = Old1 y
    aux k x ts (Singleton (TestedTerm y (t':ts'))) =
      aux k x ts (TestCase (Map.singleton t' (Singleton (TestedTerm y ts'))))
    aux k x (t:ts) (TestCase res) =
      case Map.lookup t res of
        Nothing -> New1 (k (TestCase (Map.insert t (Singleton (TestedTerm x ts)) res)))
        Just res' ->
          let k' r = k (TestCase (Map.insert t r res)) in
          aux k' x ts res'
