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
newtype Variable = Variable { varNumber :: Int } deriving (Show, Eq, Ord, Enum)

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
class (Ord ctx, Ord (VariableOf ctx), TyVars ctx) => Context ctx where
  type VariableOf ctx
  ctxEqualise :: ctx -> ctx -> Maybe (ctx, [(Type, Type)])

newtype TermContext = TermContext (Map Variable Type) deriving (Eq, Ord)
instance TyVars TermContext where
  tyVars (TermContext m) = concatMap tyVars (Map.elems m)
  tySubst f (TermContext m) = TermContext (fmap (tySubst f) m)
instance Context TermContext where
  type VariableOf TermContext = Variable
  ctxEqualise (TermContext m1) (TermContext m2) = do
    guard (Map.null (Map.intersection m1 m2))
    let m = TermContext (Map.union m1 m2)
    return (m, [])

-- A schema is a term with holes where the variables should be.
type Schema = TmIn SchemaContext

newtype SchemaContext = SchemaContext [Type] deriving (Eq, Ord, TyVars)
instance Context SchemaContext where
  type VariableOf SchemaContext = ()
  ctxEqualise (SchemaContext xs) (SchemaContext ys) =
    return (SchemaContext (xs++ys), [])

schema :: Tm -> Schema
schema t@Tm{context = TermContext m} = Tm {
  term = rename (const ()) (term t),
  context = SchemaContext (Map.elems m),
  typ = typ t
  }

-- You can instantiate a schema either by making all the variables
-- the same or by making them all different.
leastGeneral, mostGeneral :: Schema -> Tm
leastGeneral s@Tm{context = SchemaContext xs} =
  s { term = evalState (aux (term s)) xs,
      context = TermContext (Map.fromList (zip [Variable 0..] tys)) }
  where
    tys = usort xs
    names = Map.fromList (zip tys [Variable 0..])
    aux (Var ()) = do
      (ty:tys) <- get
      put tys
      return (Var (Map.findWithDefault __ ty names))
mostGeneral s@Tm{context = SchemaContext xs} =
  s { term = evalState (aux (term s)) 0,
      context = TermContext (Map.fromList (zip [Variable 0..] xs)) }
  where
    aux (Var ()) = do { n <- get; put $! n+1; return (Var (Variable n)) }
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)
