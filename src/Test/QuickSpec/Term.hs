-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor #-}
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
import qualified Data.Rewriting.Substitution.Type as T
import Octonions hiding (Fun)
import Data.List
import Data.Maybe
import Debug.Trace

-- Terms and schemas.
-- A schema is like a term but has holes instead of variables.
type TermOf = Tm Constant
type Term = TermOf Variable
type Schema = TermOf Type

-- Term ordering - size, skeleton, generality.
type Measure f v = (Int, Tm f (), Int, Tm f v)
measure :: Ord v => Tm f v -> Measure f v
measure t = (size t, rename (const ()) t, -length (usort (vars t)), t)

size :: Tm f v -> Int
size Var{} = 1
size (Fun _f xs) = 1+sum (map size xs)

-- Constants have values, while variables do not (as only monomorphic
-- variables have generators, so we need a separate defaulting phase).
data Constant =
  Constant {
    conName  :: String,
    conValue :: Value Identity }
  deriving Show
instance Eq Constant where x == y = x `compare` y == EQ
instance Ord Constant where compare = comparing conName
instance Pretty Constant where
  pretty x = text (conName x)
instance Typed Constant where
  typ = typ . conValue
  typeSubstA s (Constant name value) =
    Constant name <$> typeSubstA s value

-- We're not allowed to have two variables with the same number
-- but different type.
data Variable =
  Variable {
    varNumber :: Int,
    varType   :: Type }
  deriving Show
instance Eq Variable where x == y = x `compare` y == EQ
instance Ord Variable where compare = comparing varNumber
instance Pretty Variable where
  pretty x = text ("v" ++ show (varNumber x))
instance Typed Variable where
  typ = varType
  typeSubstA s (Variable n ty) =
    Variable n <$> typeSubstA s ty
instance CoArbitrary Variable where
  coarbitrary x = coarbitrary (varNumber x)

instance Typed v => Typed (TermOf v) where
  typ (Var x) = typ x
  typ (Fun f xs) = typeDrop (length xs) (typ f)
    where
      typeDrop 0 ty = ty
      typeDrop n (Fun Arrow [_, ty]) = typeDrop (n-1) ty

  typeSubstA s (Var x) = Var <$> typeSubstA s x
  typeSubstA s (Fun f xs) =
    Fun <$> typeSubstA s f <*> traverse (typeSubstA s) xs

instance Typed v => Apply (TermOf v) where
  adapt Var{} _ = mzero
  adapt t@(Fun f xs) u = adapt (typ t) (typ u)
  groundApply t@(Fun f xs) u =
    case typ t of
      Fun Arrow [arg, res] | arg == typ u -> Fun f (xs ++ [u])

-- Take a term and alpha-rename its type canonically.
normaliseType :: Typed a => a -> a
normaliseType t = typeSubst (evalSubst s) t
  where
    s = T.fromMap (Map.fromList (zip tvs (map (Var . TyVar) [0..])))
    tvs = tvs' ++ (usort (tyVars t) \\ tvs')
    tvs' = usort (tyVars (typ t))

-- Turn a term into a schema by forgetting about its variables.
schema :: Term -> Schema
schema = rename typ

-- Instantiate a schema by making all the variables different.
instantiate :: Schema -> Term
instantiate s = evalState (aux s) 0
  where
    aux (Var ty) = do { n <- get; put $! n+1; return (Var (Variable n ty)) }
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

-- Take a term and unify all type variables,
-- and then all variables of the same type.
skeleton :: (Ord v, Typed v) => TermOf v -> TermOf v
skeleton = normaliseType . unifyTermVars . unifyTypeVars
  where
    unifyTypeVars = typeSubst (const (Var (TyVar 0)))
    unifyTermVars t = subst (T.fromMap (Map.fromList (makeSubst (vars t)))) t
    makeSubst xs =
      [ (v, Var w) | vs@(w:_) <- partitionBy typ xs, v <- vs ]

evaluateTm :: (Typed v, Applicative f, Show v) => (v -> Value f) -> Tm Constant v -> Value f
evaluateTm env (Var v) = env v
evaluateTm env (Fun f xs) =
  foldl groundApply x (map (evaluateTm env) xs)
  where
    x = mapValue (pure . runIdentity) (conValue f)

evaluateTerm :: (CoArbitrary v, Ord v, Typed v, Show v) => (Type -> Value Gen) -> TermOf v -> Value Gen
evaluateTerm env t =
  -- The evaluation itself doesn't happen in the Gen monad but in the
  -- (StdGen, Int) reader monad. This is to avoid splitting the seed,
  -- which would cause different occurrences of the same variable
  -- to get different values!
  toGen (evaluateTm f t)
  where
    f x = fromGen (mapValue (coarbitrary x) (env (typ x)))
    toGen = mapValue (MkGen . curry)
    fromGen = mapValue (uncurry . unGen)
