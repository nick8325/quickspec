-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor, FlexibleContexts, GADTs, RecordWildCards #-}
module QuickSpec.Term where

#include "errors.h"
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import Data.List
import qualified Data.Map as Map
import Data.Ord
import QuickSpec.Type
import QuickSpec.Utils
import Test.QuickCheck hiding (subterms)
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Twee.Base
import qualified QuickSpec.Label as Label
import Data.Maybe
import qualified Data.DList as DList

-- Term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure f = (Int, Int, MeasureFuns (Extended f), Int, [Var])
measure :: (Numbered f, Sized f) => Term f -> Measure f
measure t = (size t, -length (vars t),
             MeasureFuns (skolemSkeleton (build (extended (singleton t)))), -length (usort (vars t)), vars t)

skolemSkeleton :: (Numbered f, Minimal f) => Term f -> Term f
skolemSkeleton = subst (const (con minimal))

newtype MeasureFuns f = MeasureFuns (Term f)
instance Function f => Eq (MeasureFuns f) where
  t == u = compare t u == EQ
instance Function f => Ord (MeasureFuns f) where
  compare (MeasureFuns t) (MeasureFuns u) = compareFuns t u

compareFuns :: Function f => Term f -> Term f -> Ordering
compareFuns (Var x) (Var y) = compare x y
compareFuns Var{} Fun{} = LT
compareFuns Fun{} Var{} = GT
compareFuns (App f ts) (App g us) =
  compare f g `orElse`
  compare (map MeasureFuns ts) (map MeasureFuns us)

depth :: Term f -> Int
depth Var{} = 1
depth (Fun _ ts) = 1 + maximum (0:map (succ . depth) (fromTermList ts))

-- Constants have values, while variables do not (as only monomorphic
-- variables have generators, so we need a separate defaulting phase).
data Constant =
  Constant {
    conName         :: String,
    conValue        :: Value Identity,
    conGeneralValue :: Poly (Value Identity),
    conArity        :: Int,
    conStyle        :: TermStyle,
    conSize         :: Int,
    conIsBackground :: Bool }
  | Id Type

instance Show Constant where
  show con@Constant{} = conName con
  show (Id ty) = "id[" ++ show ty ++ "]"

instance Label.Labelled Constant where
  cache = constantCache

{-# NOINLINE constantCache #-}
constantCache :: Label.Cache Constant
constantCache = Label.mkCache

instance Numbered Constant where
  fromInt n = fromMaybe __ (Label.find n)
  toInt = Label.label

idTerm :: Term Constant -> Term Constant
idTerm t = app (Id (typ t)) [t]

instance Eq Constant where x == y = x `compare` y == EQ
instance Ord Constant where
  compare = comparing f
    where
      f con@Constant{..} = Left (twiddle conArity, conName, typ conGeneralValue, typ conValue)
      f (Id ty) = Right ty
      -- This tweak is taken from Prover9
      twiddle 2 = 1
      twiddle 1 = 2
      twiddle n = n
instance Pretty Constant where
  pPrint (Id ty) = text "id[" <> pPrint ty <> text "]"
  pPrint con = text (conName con)
instance PrettyTerm Constant where
  termStyle (Id _) = invisible
  termStyle f = implicitArguments n (conStyle f)
    where
      n = implicitArity (typ (conGeneralValue f))
instance Typed Constant where
  typ (Id ty) = app Arrow [ty, ty]
  typ con = typ (conValue con)
  typeSubst_ sub (Id ty) = Id (typeSubst_ sub ty)
  typeSubst_ sub x = x { conValue = typeSubst_ sub (conValue x) }
instance Sized Constant where
  size (Id _) = 0
  size con = fromIntegral (conSize con)
instance Arity Constant where
  arity (Id _) = 1
  arity con = conArity con

implicitArity :: Type -> Int
implicitArity (App Arrow [t, u]) | isDictionary t = 1 + implicitArity u
implicitArity _ = 0

maxArity :: Constant -> Int
maxArity (Id ty) = typeArity ty
maxArity con = typeArity (typ (conGeneralValue con))

instance Typed (Term Constant) where
  typ (Var x) = ERROR("variables must be wrapped in type tags")
  typ (App f xs) = typeDrop (length xs) (typ f)
  otherTypesDL t =
    DList.fromList (funs t) >>= typesDL . fromFun

  typeSubst_ sub x@Var{} = x
  typeSubst_ sub (App f ts) = app (typeSubst sub f) (map (typeSubst sub) ts)

instance Apply (Term Constant) where
  tryApply t@(App f xs) u = do
    let f' = f { conArity = conArity f + 1 }
    guard (maxArity f > length xs)
    case typ t of
      App Arrow [arg, _] | arg == typ u -> Just (app f' (xs ++ [u]))
      _ -> Nothing

-- Instantiate a schema by making all the variables different.
instantiate :: Term Constant -> Term Constant
instantiate s = build (evalState (aux s) Map.empty)
  where
    aux (App (Id ty) [Var _]) = do
      m <- get
      let n = Map.findWithDefault 0 ty m
      put $! Map.insert ty (n+1) m
      return (fun (toFun (Id ty)) [var (MkVar n)])
    aux (Fun f xs) = fmap (fun f) (mapM aux (fromTermList xs))

-- Take a term and unify all type variables,
-- and then all variables of the same type.
skeleton :: Term Constant -> Term Constant
skeleton = unifyTermVars . unifyTypeVars
  where
    unifyTypeVars = typeSubst (const (var (MkVar 0)))
    unifyTermVars = subst (const (var (MkVar 0)))

typedVars :: Term Constant -> [(Type, Var)]
typedVars t = [(ty, x) | App (Id ty) [Var x] <- subterms t]

evaluateTm :: Applicative f => (Type -> Var -> Value f) -> Term Constant -> Value f
evaluateTm env (App (Id ty) [Var v]) = env ty v
evaluateTm env (App (Id _) [t]) = evaluateTm env t
evaluateTm env (App f xs) =
  foldl apply x (map (evaluateTm env) xs)
  where
    x = mapValue (pure . runIdentity) (conValue f)

instance CoArbitrary Var where
  coarbitrary (MkVar x) = coarbitrary x

makeValuation :: (Type -> Value Gen) -> QCGen -> Int -> Type -> Var -> Value Identity
makeValuation env g n ty x =
  mapValue (\gen -> Identity (unGen (coarbitrary x gen) g n)) (env ty)
