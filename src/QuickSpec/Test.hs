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

defaultTypes :: Typed a => Type -> a -> a
defaultTypes ty = typeSubst (const ty)

makeTester :: (a -> Term) -> (Type -> Value Gen) -> [(QCGen, Int)] -> Signature -> Type -> Maybe (Value (TypedTestSet a))
makeTester toTerm env tests sig ty = do
  i <- listToMaybe (findInstanceOf sig (defaultTypes (defaultTo_ sig) ty))
  case unwrap (i :: Value (DictOf Ord)) of
    DictOf Dict `In` w ->
      return . wrap w $
        emptyTypedTestSet (Just . reunwrap w . makeTests (env . defaultTypes (defaultTo_ sig)) tests . defaultTypes (defaultTo_ sig) . toTerm)

makeTests :: (Type -> Value Gen) -> [(QCGen, Int)] -> Term -> Value []
makeTests env tests t =
  mapValue f (evaluateTerm env t)
  where
    f :: Gen a -> [a]
    f x = map (uncurry (unGen x)) tests

env :: Signature -> Type -> Value Gen
env sig ty =
  case findInstanceOf sig ty of
    [] ->
      fromMaybe __ $
      cast ty $
      toValue (ERROR $ "missing arbitrary instance for " ++ prettyShow ty :: Gen A)
    (i:_) ->
      forValue (i :: Value (DictOf Arbitrary)) $ \(DictOf Dict) -> arbitrary

genSeeds :: Int -> IO [(QCGen, Int)]
genSeeds maxSize = do
  rnd <- newQCGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..maxSize])))

