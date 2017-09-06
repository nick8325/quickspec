{-# LANGUAGE ScopedTypeVariables,
             TypeFamilies,
             FlexibleContexts,
             DataKinds,
             Rank2Types,
             GADTs
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
type EmbType t a = Foldr (->) (TestCaseWrapped t a) a

-- A test case for predicates of type a
-- if `a ~ A -> B -> C -> Bool` we get `TestCase a ~ (A, (B, (C, ())))`
--
-- Some speedup should be possible by using unboxed tuples instead...
type TestCase a = Foldr (,) () a

data TestCaseWrapped t a = TestCaseWrapped { unTestCaseWrapped :: (TestCase a) }

instance Eq (TestCaseWrapped str a) where
  p == q = False

instance Ord (TestCaseWrapped str a) where
  compare p q = LT

-- A `suchThat` generator for a predicate
genSuchThat :: (Predicateable a, Arbitrary (TestCase a)) => a -> Gen (TestCaseWrapped x a)
genSuchThat p = TestCaseWrapped <$> arbitrary `suchThat` uncrry p

data Predicate = PRW (forall t. Typeable t => t -> PredRep)

data PredRep = PredRep { predInstances :: [Instance]
                       , selectors :: [Constant]
                       , predCons :: Constant}

-- | Declare a predicate with a given name and value.
-- The predicate should have type @... -> Bool@.
predicate :: ( Predicateable a
             , Typeable a
             , Typeable (TestCase a))
             => String -> a -> Predicate 
predicate name p = PRW $ predI name p

predI :: forall a t. ( Predicateable a,
                           Typeable a,
                           Typeable t,
                           Typeable (TestCase a)) =>
                           String -> a -> t -> PredRep 
predI name pred _ = PredRep instances
                                getters
                                predicateCons
  where
    instances =  makeInstance (\(dict :: Dict (Arbitrary (TestCase a))) -> (withDict dict genSuchThat) pred :: Gen (TestCaseWrapped t a))
              ++ names (NamesFor [name] :: NamesFor (TestCaseWrapped t a))

    getters = getrs ("prj_" ++ name) pred (unTestCaseWrapped :: TestCaseWrapped t a -> TestCase a)

    predicateCons = constant name pred

lookupPredicate :: Constant -> [PredRep] -> Maybe PredRep
lookupPredicate c []     = Nothing
lookupPredicate c (x:xs) = if conName c == conName (predCons x)
                           then Just x
                           else lookupPredicate c xs
