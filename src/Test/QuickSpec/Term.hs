-- Terms and evaluation.
{-# LANGUAGE CPP #-}
module Test.QuickSpec.Term where

#include "errors.h"
import Test.QuickSpec.Type
import Test.QuickCheck
import Data.Rewriting.Term hiding (map)
import qualified Data.Rewriting.Term as T
import qualified Data.Typeable as Ty
import qualified Data.Typeable.Internal as Ty
import Control.Monad.Trans.State.Strict

-- Terms.
type Tm = Term Constant Variable
newtype Constant = Constant { conName :: String } deriving Show
newtype Variable = Variable { varNumber :: Int } deriving Show

-- A schema is a term with holes where the variables should be.
type Schema = Term Constant ()
schema :: Tm -> Schema
schema = rename (const ())

-- You can instantiate a schema either by making all the variables
-- the same or by making them all different.
leastGeneral, mostGeneral :: Schema -> Tm
leastGeneral = rename (const (Variable 0))
mostGeneral s = evalState (aux s) 0
  where
    aux (Var ()) = do { n <- get; put $! n+1; return (Var (Variable n)) }
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

-- An expression is a term plus its value.
data Expr = Expr {
  term :: Tm,
  value :: Value Gen
  } deriving Show

-- Build expressions for constants or variables.
constantExpr :: Typeable a => String -> a -> Expr
constantExpr name x = Expr (Fun (Constant name) []) (toValue (return x))

variableExpr :: (Typeable a, Arbitrary a) => Int -> a -> Expr
variableExpr n x = Expr (Var (Variable n)) (toValue gen)
  where
    gen = coarbitrary (Ty.typeOf x) (variant n (arbitrary `asTypeOf` return x))

instance CoArbitrary Ty.TypeRep where
  coarbitrary ty =
    case Ty.splitTyConApp ty of
      (tyCon, tys) -> coarbitrary tyCon . coarbitrary tys
instance CoArbitrary Ty.TyCon where
  coarbitrary tyCon = coarbitrary (Ty.tyConHash tyCon)
instance CoArbitrary Ty.Fingerprint where
  coarbitrary (Ty.Fingerprint w1 w2) = coarbitrary w1 . coarbitrary w2

-- Build expressions for application.
instance Apply Expr where
  tryApply t@Expr{term = Fun f xs} u = do
    v <- tryApply (value t) (value u)
    return (Expr (Fun f (xs ++ [term u])) v)
  tryApply _ _ = Nothing
