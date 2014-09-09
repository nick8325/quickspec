{-# LANGUAGE CPP, ConstraintKinds #-}
module Test.QuickSpec.Eval where

#include "errors.h"
import Test.QuickSpec.Base
import Test.QuickSpec.Utils
import Test.QuickSpec.Type
import Test.QuickSpec.Term
import Test.QuickSpec.TestTree
import Test.QuickSpec.Signature
import Data.Constraint
import Data.Map(Map)
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad

data Eval a = Eval {
  ordDict :: Dict (Ord a),
  tree :: TestTree a
  }

type Evals = Map Type (Value Eval)
type Schemas = Map Int (Map Type [Schema])

collect :: [Typed a] -> Map Type [a]
collect xs =
  Map.fromList [(typ y, map untyped ys) | ys@(y:_) <- partitionBy typ xs]

typeSchemas :: [Schema] -> Map Type [Schema]
typeSchemas = fmap (map schema) . collect . map instantiate

initialSchemas :: Signature -> Schemas
initialSchemas sig = Map.fromList [(1, typeSchemas untypedSchemas)]
  where
    untypedSchemas = Var ():[Fun c [] | c <- constants sig]
  
schemasOfSize :: Int -> Schemas -> [Schema]
schemasOfSize n ss = do
  i <- [1..n-1]
  let j = n-i
  (fty, fs) <- Map.toList =<< maybeToList (Map.lookup i ss)
  guard (canApply fty (Var (TyVar 0)))
  (xty, xs) <- Map.toList =<< maybeToList (Map.lookup j ss)
  guard (canApply fty xty)
  f <- fs
  x <- xs
  return (apply f x)

-- Testing!
extend n ss = Map.insert n (typeSchemas (schemasOfSize n ss)) ss
ss1 = initialSchemas sig
ss2 = extend 2 ss1
ss3 = extend 3 ss2
ss4 = extend 4 ss3
ss5 = extend 5 ss4
