{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
module QuickSpec.Test where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Signature
import QuickSpec.TestSet
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import System.Random
import Data.Constraint
import Data.Maybe
import Data.Ord
import Control.Applicative

newtype Default = Default Int deriving (Eq, Ord, Arbitrary, CoArbitrary, Typeable)

newtype Defaulted a = Defaulted { unDefaulted :: a } deriving (Eq, Ord, Show, Pretty)

instance Typed a => Typed (Defaulted a) where
  typ = typ . unDefaulted
  typeSubstA _ x = pure x

defaulted :: Typed a => Poly a -> Defaulted a
defaulted = Defaulted . typeSubst (const ty) . mono
  where
    ty = typeOf (undefined :: Default)

makeTester :: (a -> Term) -> (Type -> Value Gen) -> [(QCGen, Int)] -> Signature -> Type -> Maybe (Value (TypedTestSet a))
makeTester toTerm env tests sig ty = do
  Instance Dict `In` w <-
    fmap unwrap (listToMaybe [ i | i <- ords sig, typ i == ty ])
  return . wrap w $
    emptyTypedTestSet (Just . reunwrap w . makeTests env tests . toTerm)

makeTests :: (Type -> Value Gen) -> [(QCGen, Int)] -> Term -> Value []
makeTests env tests t =
  mapValue f (evaluateTerm env t)
  where
    f :: Gen a -> [a]
    f x = map (uncurry (unGen x)) tests

env :: Signature -> Type -> Value Gen
env sig ty =
  case [ i | i <- arbs sig, typ i == ty ] of
    [] ->
      fromMaybe __ $
      cast ty $
      toValue (ERROR $ "missing arbitrary instance for " ++ prettyShow ty :: Gen A)
    (i:_) ->
      forValue i $ \(Instance Dict) -> arbitrary

genSeeds :: Int -> IO [(QCGen, Int)]
genSeeds maxSize = do
  rnd <- newQCGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..maxSize])))

