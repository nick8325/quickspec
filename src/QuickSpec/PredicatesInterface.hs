{-# LANGUAGE ScopedTypeVariables #-}
module QuickSpec.PredicatesInterface where
import QuickSpec.Term
import Test.QuickCheck
import Data.Dynamic

fromJust (Just x) = x

class Predicateable a where
    toPredicates :: a -> Gen (Maybe [Dynamic]) 
    getters      :: Int -> String -> a -> [Int -> Constant]
    size         :: a -> Int

instance Predicateable Bool where
    toPredicates True  = return (Just [])
    toPredicates False = return Nothing
    getters _ _ _ = []
    size _ = 0

instance (Predicateable b, Typeable a, Arbitrary a) => Predicateable (a -> b) where
    getters indx name _ =
        (:)
        (\i ->
            constant
                (name++show indx)
                (extract i :: Predicates -> a))
        (map (\f -> f . (1+)) (getters (indx+1) name (undefined :: b)))

    -- here is where we could do the lazy predicate stuff for an instance
    toPredicates predicate = do
                                a <- arbitrary
                                dyns <- toPredicates (predicate a)
                                return $ fmap ((toDyn a):) dyns

    size _ = 1 + size (undefined :: b)

extract :: (Typeable a) => Int -> Predicates -> a
extract i (P preds) = fromJust $ fromDynamic $ preds `at` i

at :: [(Int, [a])] -> Int -> a
at [] _ = undefined
at ((j, xs):tl) i
    | i < j     = xs !! i
    | otherwise = tl `at` (i-j)

-- A type to hold _all_ predicates,
-- I imagine we will keep this type
-- hidden in QuickSpec
data Predicates = P {unP :: [(Int, [Dynamic])]} deriving(Show)-- Arity + arguments

-- Dummy instances, don't matter since we never inspect
-- the type (only it's projections)
instance Eq Predicates where
    p == q = False

instance Ord Predicates where
    compare p q = LT

type PredicateRep = (((Int, Gen (Maybe [Dynamic])), [Int -> Constant]), Constant)

predicate :: (Predicateable a, Typeable a) => String -> a -> PredicateRep
predicate name p = (((size p, toPredicates p), getters 0 name p), constant name p)

predicateGen :: (Predicateable a, Typeable a) => String -> a -> Gen [Dynamic] -> PredicateRep
predicateGen name p g = (((size p, fmap Just g), getters 0 name p), constant name p)

preds :: [PredicateRep] -> (Gen Predicates, [Constant])
preds xs = resolvePredicates $ unzip (map fst xs)

resolvePredicates :: ([(Int, Gen (Maybe [Dynamic]))], [[Int -> Constant]]) -> (Gen Predicates, [Constant])
resolvePredicates (gen, getters) = (makeGen, concat $ zipWith (\fs i -> map ($i) fs) getters [0..])
    where
        makeOneGen :: (Int, Gen (Maybe [Dynamic])) -> Gen (Int, [Dynamic])
        makeOneGen (i, generator) = do
                                     v <- backtracking generator
                                     return (i, v)
        
        makeGen = fmap P $ sequence $ map makeOneGen gen

backtracking :: Gen (Maybe a) -> Gen a
backtracking g = do
                    x <- g
                    i <- resize 10 arbitrary
                    case x of
                        Nothing -> backtracking (scale (\j -> max (j+i) 0) g) -- We failed
                                                                              -- so we arbitrarily increase the size
                                                                              -- which is probably a bad idea in general
                        Just y  -> return y

makeContexts reps = zipWith (\((_, fns), p) i -> (p, map ($i) fns)) reps [0..]
