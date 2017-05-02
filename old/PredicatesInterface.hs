{-# LANGUAGE ScopedTypeVariables,
             TypeFamilies,
             FlexibleContexts,
             DataKinds
#-}
module QuickSpec.PredicatesInterface where
import Data.Constraint
import Data.Maybe
import QuickSpec.Term
import QuickSpec.Instance
import Test.QuickCheck
import Data.Dynamic
import Data.List
import GHC.TypeLits

class Predicateable a where
  uncrry       :: a -> TestCase a -> Bool
  getrs        :: (Typeable x) => String -> a -> (x -> TestCase a) -> [Constant]

instance Predicateable Bool where
  uncrry       = const 
  getrs _ _ _  = []

instance forall a b. (Predicateable b, Typeable a, TestCase (a -> b) ~ (a, TestCase b)) => Predicateable (a -> b) where
  uncrry f (a, b) = uncrry (f a) b
  getrs s _ (foo :: x -> (a, TestCase b)) = constant s (fst . foo :: x -> a) : getrs (s++"'") (undefined :: b) (snd . foo :: x -> TestCase b)

-- Foldr over functions
type family (Foldr f b fun) :: * where
  Foldr f def (a -> b) = f a (Foldr f def b)
  Foldr f def b        = def

-- Calculate the type of the "embedding" function,
-- the _uninterpreted_ function which we add when pruning
-- in the "(extract n) (toP x1 x2 ... xn ... xm) = xn" step
type EmbType (str :: Symbol) a = Foldr (->) (TestCaseWrapped str a) a

-- A test case for predicates of type a
-- if `a ~ A -> B -> C -> Bool` we get `TestCase a ~ (A, (B, (C, ())))`
--
-- Some speedup should be possible by using unboxed tuples instead...
type TestCase a = Foldr (,) () a

data TestCaseWrapped (str :: Symbol) a = TestCaseWrapped { unTestCaseWrapped :: (TestCase a) }

instance Eq (TestCaseWrapped str a) where
  p == q = False

instance Ord (TestCaseWrapped str a) where
  compare p q = LT

-- A `suchThat` generator for a predicate
genSuchThat :: (Predicateable a, Arbitrary (TestCase a)) => a -> Gen (TestCaseWrapped x a)
genSuchThat p = TestCaseWrapped <$> arbitrary `suchThat` uncrry p

data PredRep = PredRep {predInstances :: [Instance], selectors :: [Constant], predCons :: Constant, embedder :: Constant}

predicate :: forall a str. (KnownSymbol str,
                            Predicateable a,
                            Typeable a,
                            Typeable (EmbType str a),
                            Typeable (TestCase a)) => (Proxy (str :: Symbol)) -> a -> PredRep 
predicate proxy pred = PredRep instances
                               getters
                               predicateCons
                               embedder
  where
    instances =  makeInstance (\(dict :: Dict (Arbitrary (TestCase a))) -> (withDict dict genSuchThat) pred :: Gen (TestCaseWrapped str a))
              ++ names (NamesFor [symbolVal proxy] :: NamesFor (TestCaseWrapped str a))

    getters = getrs ("prj_" ++ symbolVal proxy) pred (unTestCaseWrapped :: TestCaseWrapped str a -> TestCase a)

    predicateCons = constant (symbolVal proxy) pred

    embedder = constant ("emb_" ++ symbolVal proxy) (undefined :: EmbType str a)

lookupPredicate :: Constant -> [PredRep] -> Maybe PredRep
lookupPredicate c []     = Nothing
lookupPredicate c (x:xs) = if conName c == conName (predCons x)
                           then Just x
                           else lookupPredicate c xs
