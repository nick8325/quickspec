-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
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
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import Data.Ord

-- Contexts, parametrised over the type of variables
-- (which is different between terms and schemas).
newtype Context v = Context { unContext :: Map v VarType } deriving Show
type VarType = Value Gen

instance Ord v => Eq (Context v) where
  x == y = compare x y == EQ
instance Ord v => Ord (Context v) where
  compare = comparing (\(Context x) -> fmap typeOfValue x)

-- Typed terms, parametrised over the type of variables.
type Tm = TmOf Variable
data TmOf v = Tm {
  term    :: TermOf v,
  context :: Context v,
  typ     :: Type
  } deriving (Eq, Show)
type TermOf = Term Constant

-- Constants and variables.
-- Constants have values, while variables do not have values (their
-- generators are stored in the context).
data Constant = Constant { conName :: String, conValue :: Value Identity } deriving Show
instance Eq Constant where
  x == y = compare x y == EQ
instance Ord Constant where
  compare = comparing (\x -> (conName x, typeOfValue (conValue x)))

newtype Variable = Variable { varNumber :: Int } deriving (Show, Eq, Ord, Enum)
instance TyVars Variable where
  tyVars _ = []
  tySubst _ x = x

instance Ord v => Ord (TmOf v) where
  compare = comparing $ \t -> (measure (term t), term t, context t, typ t)

-- Term ordering - size, generality, skeleton.
type Measure f = (Int, Int, Term f ())
measure :: Ord v => Term f v -> Measure f
measure t = (size t, length (usort (vars t)), rename (const ()) t)

size :: Term f v -> Int
size Var{} = 0
size (Fun f xs) = 1+sum (map size xs)

-- How to apply terms.
instance TyVars v => TyVars (TmOf v) where
  tyVars t = tyVars (typ t) ++ tyVars (Map.elems (unContext (context t)))
  tySubst f t =
    t { term = rename (tySubst f) (term t),
        context = Context (fmap (tySubst f) (unContext (context t))),
        typ = tySubst f (typ t) }

instance (Ord v, TyVars v) => Apply (TmOf v) where
  tyApply f x = do
    (ctx, cs) <- lift (lift (equaliseContexts (context f) (context x)))
    lift (tell cs)
    (f', x') <- tyApply (typ f) (typ x)
    return (f { context = ctx, typ = f' },
            x { context = ctx, typ = x' })
  tyGroundApply f x | context f == context x =
    Tm { term = app (term f) (term x),
         context = context f,
         typ = tyGroundApply (typ f) (typ x) }
    where
      app (Fun f xs) t = Fun f (xs ++ [t])

equaliseContexts (Context m1) (Context m2) = do
  guard (Map.null (Map.intersection m1 m2))
  return (Context (Map.union m1 m2), [])

-- A schema is a term with holes where the variables should be.
type Schema = TmOf VarType

schema :: Tm -> Schema
schema t =
  Tm { term = rename f (term t),
       context = Context Map.empty,
       typ = typ t }
  where
    f x = Map.findWithDefault __ x (unContext (context t))

-- You can instantiate a schema either by making all the variables
-- the same or by making them all different.
leastGeneral, mostGeneral :: Schema -> Tm
leastGeneral s =
  s { term = rename f (term s),
      context = Context (Map.fromList (zip [Variable 0..] tys)) }
  where
    tys = usortBy (comparing typeOfValue) (vars (term s))
    names = Map.fromList (zip (map typeOfValue tys) [Variable 0..])
    f x = Map.findWithDefault __ (typeOfValue x) names
mostGeneral s =
  s { term = evalState (aux (term s)) 0,
      context = Context (Map.fromList (zip [Variable 0..] (vars (term s)))) }
  where
    aux (Var _) = do { n <- get; put $! n+1; return (Var (Variable n)) }
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

con :: String -> Value Identity -> TmOf v
con c x =
  Tm { term = Fun (Constant c x) [],
       context = Context Map.empty,
       typ = typeOfValue x }

hole :: Value Gen -> Schema
hole x =
  Tm { term = Var x,
       context = Context Map.empty,
       typ = typeOfValue x }

var :: Value Gen -> Int -> Tm
var x n =
  Tm { term = Var (Variable n),
       context = Context (Map.singleton (Variable n) x'),
       typ = typeOfValue x }
  where
    x' = injectValue (variant n) x
