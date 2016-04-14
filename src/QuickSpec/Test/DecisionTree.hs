-- Decision trees for testing terms for equality.
module QuickSpec.Test.DecisionTree where

import Control.Monad
import Data.Constraint
import qualified Data.Map as Map
import Data.Map(Map)
import QuickSpec.Type
import QuickSpec.Term
import Data.Functor.Identity

data DecisionTree f =
  DecisionTree {
    ordDict  :: Type -> Maybe (Value OrdDict),
    evaluate :: (Var -> Value Identity) -> Term f -> Value Identity,
    test     :: Term f -> Term f -> Maybe (Var -> Value Identity),
    tests    :: [Var -> Value Identity],
    tree     :: Map Type (Value (TypedDecisionTree f))
    }

newtype OrdDict a = Dict (Ord a)

data TypedDecisionTree t a =
    TestCase (Map a (TypedDecisionTree t a))
  | Singleton (Tested t a)

data Tested t a =
  Tested {
    testedTerm  :: t,
    tests :: [a] }

emptyDecisionTree :: (Type -> Maybe (Value (TypedDecisionTree t))) -> DecisionTree t
emptyDecisionTree makeType = DecisionTree makeType Map.empty

emptyTypedDecisionTree :: Ord a => (t -> Maybe [a]) -> TypedDecisionTree t a
emptyTypedDecisionTree makeTerm = TypedDecisionTree makeTerm Dict (TestCase Map.empty)

data Result t = New (DecisionTree t) | Old t

findDecisionTree :: Typed t => t -> DecisionTree t -> Maybe (Value (TypedDecisionTree t))
findDecisionTree x ts =
  Map.lookup (typ x) (testSet ts) `mplus`
  makeType ts (typ x)

insert :: Typed t => t -> DecisionTree t -> Maybe (Result t)
insert x ts = do
  tts `In` w <- fmap unwrap (findDecisionTree x ts)
  tt <- fmap (Tested x) (makeTerm tts x)
  return $
    case insert1 tt tts of
      New1 tts ->
        New ts { testSet = Map.insert (typ x) (wrap w tts) (testSet ts) }
      Old1 t ->
        Old t

data Result1 t a = New1 (TypedDecisionTree t a) | Old1 t

insert1 :: Typed t => Tested t a -> TypedDecisionTree t a -> Result1 t a
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

statistics :: TypedDecisionTree t a -> (Int, Int)
statistics (Singleton _) = (1, 0)
statistics (TestCase rs) = (sum (map fst ss), sum [ m + n | (m, n) <- ss ])
  where
    ss = map statistics (Map.elems rs)

numTests :: DecisionTree t -> Int
numTests =
  sum . map (ofValue (snd . statistics . testResults)) . Map.elems . testSet

numTerms :: DecisionTree t -> Int
numTerms =
  sum . map (ofValue (fst . statistics . testResults)) . Map.elems . testSet
