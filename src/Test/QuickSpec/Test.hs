{-# LANGUAGE CPP #-}
module Test.QuickSpec.Test where

#include "errors.h"
import Test.QuickSpec.Base
import Test.QuickSpec.Term
import Test.QuickSpec.Type
import Test.QuickSpec.Signature
import Test.QuickSpec.TestSet
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import System.Random
import Data.Constraint
import Data.Maybe

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
      toValue (ERROR $ "missing arbitrary instance for " ++ prettyShow ty :: Gen A)
    (i:_) ->
      forValue i $ \(Instance Dict) -> arbitrary


genSeeds :: Int -> IO [(QCGen, Int)]
genSeeds maxSize = do
  rnd <- newQCGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..maxSize])))

