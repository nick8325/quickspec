{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
module QuickSpec.Test where

#include "errors.h"
import Data.Constraint
import Data.Maybe
import QuickSpec.Base
import QuickSpec.Signature
import QuickSpec.Term
import QuickSpec.TestSet
import QuickSpec.Type
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

defaultTypes :: Typed a => Type -> a -> a
defaultTypes ty = typeSubst (const ty)

makeTester :: (a -> Term) -> (Type -> Value Gen) -> [(QCGen, Int)] -> Signature -> Type -> Maybe (Value (TypedTestSet a))
makeTester toTerm env tests sig ty = do
  let obsTests = [(fst (split g), n) | (g, n) <- tests]
      varTests = [(snd (split g), n) | (g, n) <- tests]
  i <- listToMaybe (findInstanceOf sig (defaultTypes (defaultTo_ sig) ty))
  case unwrap (i :: Value Observe1) of
    Observe1 obs `In` w ->
      case unwrap obs of
        Observe Dict eval `In` w' -> do
          let eval' (g, n) x = unGen (eval x) g n
          return . wrap w' $
            emptyTypedTestSet (Just . zipWith eval' obsTests . reunwrap w . makeTests (env . defaultTypes (defaultTo_ sig)) varTests . defaultTypes (defaultTo_ sig) . toTerm)

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

