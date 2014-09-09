-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
module Test.QuickSpec.Term where

#include "errors.h"
import Test.QuickSpec.Utils
import Test.QuickSpec.Base
import Test.QuickSpec.Type
import Test.QuickCheck
import Test.QuickCheck.Gen
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Ord
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Functor.Identity
import Control.Applicative
import Data.Traversable(traverse)

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
instance TyVars Variable where typeSubstA _ = pure

instance Ord v => Ord (TermOf v) where
  compare = comparing $ \t -> (measure (term t), term t, context t, typ t)

-- Term ordering - size, generality, skeleton.
type Measure f = (Int, Int, Tm f ())
measure :: Ord v => Tm f v -> Measure f
measure t = (size t, length (usort (vars t)), rename (const ()) t)

size :: Tm f v -> Int
size Var{} = 0
size (Fun _f xs) = 1+sum (map size xs)

-- How to apply terms.
instance TyVars v => TyVars (TermOf v) where
  typeSubstA f (Term t ctx ty) =
    Term t <$> typeSubstA f ctx <*> typeSubstA f ty
instance (Ord v, TyVars v) => Typed (TermOf v) where
  adapt f x = do
    adapt (context f) (context x)
    adapt (typ f) (typ x)
  groundApply f x =
    Term { term = app (term f) (term x),
           context = groundApply (context f) (context x),
           typ = groundApply (typ f) (typ x) }
    where
      app (Fun f xs) t = Fun f (xs ++ [t])

instance TyVars v => TyVars (Map k v) where
  typeSubstA f = traverse (typeSubstA f)
instance (Ord k, Eq v, Typed v) => Typed (Map k v) where
  adapt m1 m2 = equaliseContexts m1 m2
  groundApply m1 m2 = Map.union m1 m2

equaliseContexts :: (Ord k, Eq v, Typed v) => Map k v -> Map k v -> UnifyM ()
equaliseContexts m1 m2 = guard (Map.null conflicts)
  where
    conflicts = maybeIntersection check m1 m2
    maybeIntersection f = Map.mergeWithKey (const f) (const Map.empty) (const Map.empty)
    check x y
      | x == y = Nothing
      | otherwise = Just ()

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
    f n x = (Variable n, mapValue (variant n) x)

con :: String -> Value Identity -> TermOf v
con c x =
  Term { term = Fun (Constant c x) [],
         context = Map.empty,
         typ = valueType x }

hole :: Value Gen -> Schema
hole x =
  Term { term = Var x,
         context = Map.empty,
         typ = valueType x }

var :: Value Gen -> Int -> Term
var x n =
  Term { term = Var (Variable n),
         context = Map.singleton (Variable n) x',
         typ = valueType x }
  where
    x' = mapValue (variant n) x

evaluateTm :: Applicative f => (v -> Value f) -> Tm Constant v -> Value f
evaluateTm env (Var v) = env v
evaluateTm env (Fun f xs) =
  foldl apply x (map (evaluateTm env) xs)
  where
    x = mapValue (pure . runIdentity) (conValue f)

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
    toGen = mapValue (MkGen . curry)
    fromGen = mapValue (uncurry . unGen)
