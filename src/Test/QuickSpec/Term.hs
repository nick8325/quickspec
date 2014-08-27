-- Terms and evaluation.
{-# LANGUAGE CPP, TypeFamilies, FlexibleContexts, StandaloneDeriving, GeneralizedNewtypeDeriving #-}
module Test.QuickSpec.Term where

#include "errors.h"
import Test.QuickSpec.Utils
import Test.QuickSpec.Base
import Test.QuickSpec.Type
import Test.QuickCheck
import qualified Data.Typeable as Ty
import qualified Data.Typeable.Internal as Ty
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Ord
import Data.Map(Map)
import qualified Data.Map as Map

-- Typed terms, parametrised over the type of contexts
-- (which is different between terms and schemes).
data TmIn ctx = Tm {
  term    :: Term Constant (VariableOf ctx),
  context :: ctx,
  typ     :: Type
  }
deriving instance Context ctx => Eq (TmIn ctx)

type Tm = TmIn TermContext
newtype Constant = Constant { conName :: String } deriving (Show, Eq, Ord)
newtype Variable = Variable { varNumber :: Int } deriving (Show, Eq, Ord)

instance Context ctx => Ord (TmIn ctx) where
  compare = comparing $ \t -> (measure (term t), term t, context t, typ t)

-- Term ordering - size, generality, skeleton.
type Measure f = (Int, Int, Term f ())
measure :: Ord v => Term f v -> Measure f
measure t = (size t, length (usort (vars t)), rename (const ()) t)

size :: Term f v -> Int
size Var{} = 0
size (Fun f xs) = 1+sum (map size xs)

-- Ordinary terms.
class (Ord ctx, Ord (VariableOf ctx), Apply ctx, TyVars ctx) => Context ctx where
  type VariableOf ctx

newtype TermContext = TermContext (Map Variable Type) deriving (Eq, Ord)
instance Apply TermContext where
  tryApply (TermContext m1) (TermContext m2) = do
    guard (Map.null (Map.intersection m1 m2))
    return (TermContext (Map.union m1 m2))
instance TyVars TermContext where
  tyVars (TermContext m) = concatMap tyVars (Map.elems m)
  mapTyVars f (TermContext m) = TermContext (fmap (mapTyVars f) m)
instance Context TermContext where
  type VariableOf TermContext = Variable

-- A schema is a term with holes where the variables should be.
type Schema = TmIn SchemaContext

newtype SchemaContext = SchemaContext [Type] deriving (Eq, Ord, TyVars)
instance Apply SchemaContext where
  tryApply (SchemaContext xs) (SchemaContext ys) = return (SchemaContext (xs ++ ys))
instance Context SchemaContext where
  type VariableOf SchemaContext = ()

schema :: Tm -> Schema
schema t@Tm{context = TermContext m} = Tm {
  term = rename (const ()) (term t),
  -- We represent a schema as a term with an empty context
  -- (which is filled in when we instantiate the schema).
  context = SchemaContext (Map.elems m),
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
