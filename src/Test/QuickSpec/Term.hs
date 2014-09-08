-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
module Test.QuickSpec.Term where

#include "errors.h"
import Test.QuickSpec.Utils
import Test.QuickSpec.Base
import Test.QuickSpec.Type
import Test.QuickCheck
import Test.QuickCheck.Gen
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
import Control.Applicative

-- Typed terms, parametrised over the type of variables.
type Term = TermOf Variable
data TermOf v =
  Term {
    term    :: Tm Constant v,
    context :: Map v VarType,
    typ     :: Type }
  deriving (Eq, Show)
type VarType = Value Gen

-- Constants and variables.
-- Constants have values, while variables do not have values (their
-- generators are stored in the context).
data Constant =
  Constant {
    conName  :: String,
    conValue :: Value Identity }
  deriving (Show, Eq, Ord)

newtype Variable = Variable { varNumber :: Int } deriving (Show, Eq, Ord, Enum)
instance TyVars Variable where
  tyVars _ = []
  tySubst _ x = x

instance Ord v => Ord (TermOf v) where
  compare = comparing $ \t -> (measure (term t), term t, context t, typ t)

-- Term ordering - size, generality, skeleton.
type Measure f = (Int, Int, Tm f ())
measure :: Ord v => Tm f v -> Measure f
measure t = (size t, length (usort (vars t)), rename (const ()) t)

size :: Tm f v -> Int
size Var{} = 0
size (Fun f xs) = 1+sum (map size xs)

-- How to apply terms.
instance TyVars v => TyVars (TermOf v) where
  tyVars t = tyVars (typ t) ++ tyVars (Map.elems (context t))
  tySubst f t =
    t { term = rename (tySubst f) (term t),
        context = fmap (tySubst f) (context t),
        typ = tySubst f (typ t) }

instance (Ord v, TyVars v) => Apply (TermOf v) where
  tyApply f x = do
    (ctx, cs) <- lift (lift (equaliseContexts (context f) (context x)))
    lift (tell cs)
    (f', x') <- tyApply (typ f) (typ x)
    return (f { context = ctx, typ = f' },
            x { context = ctx, typ = x' })
  tyGroundApply f x | context f == context x =
    Term { term = app (term f) (term x),
           context = context f,
           typ = tyGroundApply (typ f) (typ x) }
    where
      app (Fun f xs) t = Fun f (xs ++ [t])

equaliseContexts m1 m2 = do
  guard (Map.null (Map.intersection m1 m2))
  return (Map.union m1 m2, [])

-- A schema is a term with holes where the variables should be.
type Schema = TermOf VarType

schema :: Term -> Schema
schema t =
  Term { term = rename f (term t),
         context = Map.empty,
         typ = typ t }
  where
    f x = Map.findWithDefault __ x (context t)

-- You can instantiate a schema either by making all the variables
-- the same or by making them all different.
leastGeneral, mostGeneral :: Schema -> Term
leastGeneral s =
  s { term = rename f (term s),
      context = Map.fromList (zip [Variable 0..] tys) }
  where
    tys = usort (vars (term s))
    names = Map.fromList (zip tys [Variable 0..])
    f x = Map.findWithDefault __ x names
mostGeneral s =
  s { term = evalState (aux (term s)) 0,
      context = Map.fromList (zipWith f [0..] (vars (term s))) }
  where
    aux (Var _) = do { n <- get; put $! n+1; return (Var (Variable n)) }
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)
    f n x = (Variable n, injectValue (variant n) x)

con :: String -> Value Identity -> TermOf v
con c x =
  Term { term = Fun (Constant c x) [],
         context = Map.empty,
         typ = typeOfValue x }

hole :: Value Gen -> Schema
hole x =
  Term { term = Var x,
         context = Map.empty,
         typ = typeOfValue x }

var :: Value Gen -> Int -> Term
var x n =
  Term { term = Var (Variable n),
         context = Map.singleton (Variable n) x',
         typ = typeOfValue x }
  where
    x' = injectValue (variant n) x

evaluateTm :: Applicative f => (v -> Value f) -> Tm Constant v -> Value f
evaluateTm env (Var v) = env v
evaluateTm env (Fun f xs) =
  foldl apply x (map (evaluateTm env) xs)
  where
    x = injectValue (pure . runIdentity) (conValue f)

evaluateSchema :: Schema -> Value Gen
evaluateSchema t = evaluateTm id (term t)

evaluateTerm :: Term -> Value Gen
evaluateTerm t =
  -- The evaluation itself doesn't happen in the Gen monad but in the
  -- (StdGen, Int) reader monad. This is to avoid splitting the seed,
  -- which would cause different occurrences of the same variable
  -- to get different values!
  toGen (evaluateTm f (term t))
  where
    f x = fromGen (Map.findWithDefault __ x (context t))
    toGen = injectValue (MkGen . curry)
    fromGen = injectValue (uncurry . unGen)
