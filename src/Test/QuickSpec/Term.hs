-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances #-}
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
import Data.Tuple

-- Terms and schemas.
-- A schema is like a term but has holes instead of variables.
type TermOf = Tm Constant
type Term = TermOf Variable
type Schema = TermOf ()

-- Term ordering - size, skeleton, generality.
type Measure f v = (Int, Tm f (), Int, Tm f v)
measure :: Ord v => Tm f v -> Measure f v
measure t = (size t, rename (const ()) t, length (usort (vars t)), t)

size :: Tm f v -> Int
size Var{} = 0
size (Fun _f xs) = 1+sum (map size xs)

-- Constants have values, while variables do not (as only monomorphic
-- variables have generators, so we need a separate defaulting phase).
data Constant =
  Constant {
    conName  :: String,
    conValue :: Value Identity }
  deriving Show
instance Eq Constant where x == y = x `compare` y == EQ
instance Ord Constant where
  compare = comparing (\x -> (conName x, valueType (conValue x)))

newtype Variable = Variable { varNumber :: Int } deriving (Show, Eq, Ord, Enum)

-- Applying terms.
instance TyVars (TermOf v) where typeSubstA _ = pure
instance Apply (TermOf v) where
  adapt Var{} _ = mzero
  adapt Fun{} _ = return ()
  groundApply (Fun f xs) t = Fun f (xs ++ [t])

-- Things which have a type in a certain context.
data Typed a =
  Typed {
    untyped :: a,
    context :: Map Variable Type,
    typ     :: Type }
  deriving (Eq, Ord, Show)

-- How to apply typed things.
instance TyVars a => TyVars (Typed a) where
  typeSubstA f (Typed x ctx ty) =
    Typed <$> typeSubstA f x <*> typeSubstA f ctx <*> typeSubstA f ty
instance Apply a => Apply (Typed a) where
  adapt f x = do
    adapt (untyped f) (untyped x)
    adapt (context f) (context x)
    adapt (typ f) (typ x)
  groundApply f x =
    Typed { untyped = groundApply (untyped f) (untyped x),
            context = groundApply (context f) (context x),
            typ = groundApply (typ f) (typ x) }

instance TyVars v => TyVars (Map k v) where
  typeSubstA f = traverse (typeSubstA f)
instance (Ord k, Eq v, TyVars v) => Apply (Map k v) where
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

-- Instantiate a schema by making all the variables different.
instantiate :: Schema -> Typed Term
instantiate = inferType . introduceVars

introduceVars :: Schema -> Term
introduceVars s = evalState (aux s) 0
  where
    aux (Var ()) = do { n <- get; put $! n+1; return (Var (Variable n)) }
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

inferType :: Term -> Typed Term
inferType t = typeSubst (evalSubst s) u
  where
    u = Typed {
      untyped = t,
      context = ctx,
      typ     = ty }
    Just ((ctx, ty), s) = runUnifyM (freshTyVarFor t) $ do
      ctx <- fmap Map.fromList (labelM (const (fmap Var freshTyVar)) (usort (vars t)))
      ty <- aux ctx t
      return (ctx, ty)
    aux ctx (Var x) = return (Map.findWithDefault __ x ctx)
    aux ctx (Fun f xs) = do
      tys <- mapM (aux ctx) xs
      ty <- fmap Var freshTyVar
      fty <- freshenM (valueType (conValue f))
      equalise fty (arrowType tys ty)
      return ty

-- Take a term and unify all variables of the same type.
skeleton :: Typed Term -> Typed Term
skeleton t =
  t { untyped = rename f (untyped t),
      context = Map.fromList (map swap (Map.toList names)) }
  where
    names = Map.fromList (map swap (Map.toList (context t)))
    f x = Map.findWithDefault __
            (Map.findWithDefault __ x (context t)) names

evaluateTm :: Applicative f => (v -> Value f) -> Tm Constant v -> Value f
evaluateTm env (Var v) = env v
evaluateTm env (Fun f xs) =
  foldl apply x (map (evaluateTm env) xs)
  where
    x = mapValue (pure . runIdentity) (conValue f)

evaluateTerm :: (Type -> Value Gen) -> Typed Term -> Value Gen
evaluateTerm env t =
  -- The evaluation itself doesn't happen in the Gen monad but in the
  -- (StdGen, Int) reader monad. This is to avoid splitting the seed,
  -- which would cause different occurrences of the same variable
  -- to get different values!
  toGen (evaluateTm f (untyped t))
  where
    f x@(Variable n) =
      fromGen
        (mapValue (variant n)
          (env (Map.findWithDefault __ x (context t))))
    toGen = mapValue (MkGen . curry)
    fromGen = mapValue (uncurry . unGen)

-- Testing!
app, rev :: Schema
app = Fun (Constant "app" (toValue (Identity ((++) :: [A] -> [A] -> [A])))) []
rev = Fun (Constant "rev" (toValue (Identity (reverse :: [A] -> [A])))) []
env :: Type -> Value Gen
env _ = toValue (arbitrary :: Gen [Int])
t :: Schema
t = rev `apply` (app `apply` Var () `apply` Var ())
