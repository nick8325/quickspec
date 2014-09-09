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
import Data.Maybe
import Data.Tuple

-- Typed terms, parametrised over the type of variables.
type Term = TermOf Variable
data TermOf v =
  Term {
    term    :: Tm Constant v,
    context :: Map v Type,
    typ     :: Type }
  deriving (Eq, Show)

-- Constants and variables.
-- Constants have values, while variables do not (as only monomorphic
-- variables have generators, so we need a separate defaulting phase).
data Constant =
  Constant {
    conName  :: String,
    conValue :: Value Identity }
  deriving Show
instance Eq Constant where
  x == y = x `compare` y == EQ
instance Ord Constant where
  compare = comparing (\x -> (conName x, valueType (conValue x)))

newtype Variable = Variable { varNumber :: Int } deriving (Show, Eq, Ord, Enum)
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
instance TyVars (TermOf v) where
  typeSubstA f (Term t ctx ty) =
    Term t <$> typeSubstA f ctx <*> typeSubstA f ty
instance Ord v => Typed (TermOf v) where
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
instance (Ord k, Eq v, TyVars v) => Typed (Map k v) where
  adapt m1 m2 = equaliseContexts m1 m2
  groundApply m1 m2 = Map.union m1 m2

equaliseContexts :: (Ord k, Eq v, TyVars v) => Map k v -> Map k v -> UnifyM ()
equaliseContexts m1 m2 = guard (Map.null conflicts)
  where
    conflicts = maybeIntersection check m1 m2
    maybeIntersection f = Map.mergeWithKey (const f) (const Map.empty) (const Map.empty)
    check x y
      | x == y = Nothing
      | otherwise = Just ()

-- A schema is a term with holes where the variables should be.
type Schema = TermOf ()

-- Instantiate a schema by making all the variables different.
instantiate :: Schema -> Term
instantiate = inferType . introduceVars

introduceVars :: Schema -> Term
introduceVars s =
  s { term = t,
      context =
        freshen (freshTyVarFor s)
          (Map.fromList
            [(Variable i, Var (TyVar i)) | Variable i <- vars t]) }
  where
    t = evalState (aux (term s)) 0
    aux (Var _) = do { n <- get; put $! n+1; return (Var (Variable n)) }
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

inferType :: Term -> Term
inferType t = typeSubst (evalSubst s) t
  where
    (_, s) = fromMaybe __ (runUnifyM m (freshTyVarFor t))
    m = do
      ty <- aux (term t)
      equalise ty (typ t)
    aux (Var x) = return (Map.findWithDefault __ x (context t))
    aux (Fun f xs) = do
      tys <- mapM aux xs
      ty <- fmap Var freshTyVar
      equalise (valueType (conValue f)) (arrowType tys ty)
      return ty

-- Take a term and unify all variables of the same type.
skeleton :: Term -> Term
skeleton t =
  t { term = rename f (term t),
      context = Map.fromList (map swap (Map.toList names)) }
  where
    names = Map.fromList (map swap (Map.toList (context t)))
    f x = Map.findWithDefault __
            (Map.findWithDefault __ x (context t)) names

con :: String -> Value Identity -> TermOf v
con c x =
  Term { term = Fun (Constant c x) [],
         context = Map.empty,
         typ = valueType x }

hole :: Schema
hole = Term { term = Var (), context = Map.empty, typ = Var (TyVar 0) }

evaluateTm :: Applicative f => (v -> Value f) -> Tm Constant v -> Value f
evaluateTm env (Var v) = env v
evaluateTm env (Fun f xs) =
  foldl apply x (map (evaluateTm env) xs)
  where
    x = mapValue (pure . runIdentity) (conValue f)

evaluateTerm :: (Type -> Value Gen) -> Term -> Value Gen
evaluateTerm env t =
  -- The evaluation itself doesn't happen in the Gen monad but in the
  -- (StdGen, Int) reader monad. This is to avoid splitting the seed,
  -- which would cause different occurrences of the same variable
  -- to get different values!
  toGen (evaluateTm f (term t))
  where
    f x@(Variable n) =
      fromGen
        (mapValue (variant n)
          (env (Map.findWithDefault __ x (context t))))
    toGen = mapValue (MkGen . curry)
    fromGen = mapValue (uncurry . unGen)

-- Testing!
app, rev :: Schema
app = con "app" (toValue (Identity ((++) :: [A] -> [A] -> [A])))
rev = con "rev" (toValue (Identity (reverse :: [A] -> [A])))
env :: Type -> Value Gen
env _ = toValue (arbitrary :: Gen [Int])
t :: Schema
t = rev `apply` (app `apply` hole `apply` hole)
