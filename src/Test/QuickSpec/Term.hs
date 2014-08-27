-- Terms and evaluation.
{-# LANGUAGE CPP #-}
module Test.QuickSpec.Term where

#include "errors.h"
import Test.QuickSpec.Utils
import Test.QuickSpec.Base
import Test.QuickSpec.Type
import Test.QuickCheck
import qualified Data.Typeable as Ty
import qualified Data.Typeable.Internal as Ty
import Control.Monad.Trans.State.Strict
import Data.Ord
import Data.Map(Map)
import qualified Data.Map as Map

-- Typed terms.
data TmOf v = Tm {
  term    :: Term Constant v,
  context :: Map v Type,
  typ     :: Type
  } deriving Eq
type Tm = TmOf Variable
newtype Constant = Constant { conName :: String } deriving (Show, Eq, Ord)
newtype Variable = Variable { varNumber :: Int } deriving (Show, Eq, Ord)

instance Ord v => Ord (TmOf v) where
  compare = comparing $ \t -> (measure (term t), term t, context t, typ t)

-- Term ordering - size, generality, skeleton.
type Measure f = (Int, Int, Term f ())
measure :: Ord v => Term f v -> Measure f
measure t = (size t, length (usort (vars t)), rename (const ()) t)

size :: Term f v -> Int
size Var{} = 0
size (Fun f xs) = 1+sum (map size xs)

-- A schema is a term with holes where the variables should be.
type Schema = TmOf ()

schema :: Tm -> Schema
schema t = Tm {
  term = rename (const ()) (term t),
  -- We represent a schema as a term with an empty context
  -- (which is filled in when we instantiate the schema).
  context = Map.empty,
  typ = typ t
  }

-- You can instantiate a schema either by making all the variables
-- the same or by making them all different.
-- leastGeneral, mostGeneral :: Schema -> Tm
-- leastGeneral (Schema t) = rename (const (Variable 0)) t
-- mostGeneral (Schema t) = evalState (aux t) 0
--   where
--     aux (Var ()) = do { n <- get; put $! n+1; return (Var (Variable n)) }
--     aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

-- -- An expression is a term plus its value.
-- data Expr = Expr {
--   term :: Tm,
--   value :: Value Gen
--   } deriving Show

-- -- Build expressions for constants or variables.
-- constantExpr :: Typeable a => String -> a -> Expr
-- constantExpr name x = Expr (Fun (Constant name) []) (toValue (return x))

-- variableExpr :: (Typeable a, Arbitrary a) => Int -> a -> Expr
-- variableExpr n x = Expr (Var (Variable n)) (toValue gen)
--   where
--     gen = variant n (arbitrary `asTypeOf` return x)

-- -- Build expressions for application.
-- instance Apply Expr where
--   tryApply t@Expr{term = Fun f xs} u = do
--     v <- tryApply (value t) (value u)
--     return (Expr (Fun f (xs ++ [term u])) v)
--   tryApply _ _ = Nothing
