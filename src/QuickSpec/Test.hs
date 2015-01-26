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
import Control.Monad

defaultTypes :: Typed a => Type -> a -> a
defaultTypes ty = typeSubst (const ty)

makeTester :: (a -> Term) -> (Type -> Value Gen) -> [(QCGen, Int)] -> Signature -> Type -> Maybe (Value (TypedTestSet a))
makeTester toTerm env tests sig ty = do
  i <- listToMaybe (findInstanceOf sig (defaultTypes (defaultTo_ sig) ty))
  case unwrap (i :: Value Observe1) of
    Observe1 obs `In` w ->
      case unwrap obs of
        Observe Dict eval `In` w' ->
          return . wrap w' $
            emptyTypedTestSet (tester (defaultTypes (defaultTo_ sig) . toTerm) env tests (reunwrap w >=> eval))

tester :: Ord b => (a -> Term) -> (Type -> Value Gen) -> [(QCGen, Int)] -> (Value Gen -> Gen b) -> a -> Maybe [b]
tester toTerm env tests eval t =
  Just . f $ eval (evaluateTerm env (toTerm t))
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
    (i:_) -> i

genSeeds :: Int -> IO [(QCGen, Int)]
genSeeds maxSize = do
  rnd <- newQCGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..maxSize])))

