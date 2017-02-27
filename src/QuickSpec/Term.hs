-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor, FlexibleContexts, GADTs, RecordWildCards #-}
module QuickSpec.Term where

#include "errors.h"
import Data.Char
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
import qualified Twee.Label as Label
import Data.Maybe
import qualified Data.DList as DList

-- Term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure = (Int, Int, MeasureFuns (Extended Constant), Int, [Var])
measure :: Term Constant -> Measure
measure t =
  (size t, -length (vars' t),
   MeasureFuns (build (skel (buildList (extended (singleton t))))),
   -length (usort (vars' t)), vars' t)
  where
    vars' = map snd . filter (not . isDictionary . fst) . typedVars
    skel Empty = mempty
    skel (Cons (Var x) ts) = con minimal `mappend` skel ts
    skel (Cons (Fun f ts) us) =
      case fromFun f of
        Function (Id _) -> skel ts `mappend` skel us
        _ -> fun f (skel ts) `mappend` skel us

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
depth (Fun _ ts) = 1 + maximum (0:map depth (fromTermList ts))

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
  | Apply Type

instance Show Constant where
  show con@Constant{} = conName con
  show (Id ty) = "id[" ++ show ty ++ "]"
  show (Apply ty) = "apply[" ++ show ty ++ "]"

instance Label.Labelled Constant where
  cache = constantCache

{-# NOINLINE constantCache #-}
constantCache :: Label.Cache Constant
constantCache = Label.mkCache

instance Numbered Constant where
  fromInt n = fromMaybe __ (Label.find n)
  toInt = Label.label

instance Eq Constant where x == y = x `compare` y == EQ
instance Ord Constant where
  compare = comparing f
    where
      f con@Constant{..} = Left (twiddle (conArity - implicitArity (typ conGeneralValue)), conName, typ conGeneralValue, typ conValue)
      f (Apply ty) = Right (Left ty)
      f (Id ty) = Right (Right ty)
      -- This tweak is taken from Prover9
      twiddle 2 = 1
      twiddle 1 = 2
      twiddle n = n
instance Pretty Constant where
  pPrint (Apply ty) = text "apply[" <> pPrint ty <> text "]"
  pPrint (Id ty) = text "id[" <> pPrint ty <> text "]"
  pPrint con = text (conName con)
instance PrettyTerm Constant where
  termStyle (Apply _) = invisible
  termStyle (Id _) = invisible
  termStyle f = implicitArguments n (conStyle f)
    where
      n = implicitArity (typ (conGeneralValue f))
instance Typed Constant where
  typ (Apply ty) = app Arrow [ty, ty]
  typ (Id ty) = app Arrow [ty, ty]
  typ con = typ (conValue con)
  typeReplace sub (Apply ty) = Apply (typeReplace sub ty)
  typeReplace sub (Id ty) = Id (typeReplace sub ty)
  typeReplace sub x = x { conValue = typeReplace sub (conValue x) }
instance Sized Constant where
  size (Apply _) = 0
  size (Id _) = 0
  size con = fromIntegral (conSize con)
instance Arity Constant where
  arity (Apply _) = 2
  arity (Id _) = 1
  arity con = conArity con

implicitArity :: Type -> Int
implicitArity (App Arrow [t, u]) | isDictionary t = 1 + implicitArity u
implicitArity _ = 0

instance Typed (Term Constant) where
  typ (Var x) = ERROR("variables must be wrapped in type tags")
  typ (App f xs) = typeDrop (length xs) (typ f)
  otherTypesDL t =
    DList.fromList (funs t) >>= typesDL . fromFun

  typeReplace sub x@Var{} = x
  typeReplace sub (App f ts) = app (typeReplace sub f) (map (typeReplace sub) ts)

instance Apply (Term Constant) where
  tryApply t@(App Constant{} xs) u = tryApply' t u
  tryApply t u = do
    let ty = typ t
    tryApply ty (typ u)
    return (app (Apply ty) [t, u])

tryApply' :: Term Constant -> Term Constant -> Maybe (Term Constant)
tryApply' t@(App f@Constant{} xs) u = do
  let f' = f { conArity = conArity f + 1 }
  guard (typeArity (typ (conGeneralValue f)) > length xs)
  case typ t of
    App Arrow [arg, _] | arg == typ u -> Just (app f' (xs ++ [u]))
    _ -> Nothing
tryApply' _ _ = Nothing

-- | Instantiate a schema by making all the variables different.
instantiate :: Term Constant -> Term Constant
instantiate s = build (evalState (aux s) Map.empty)
  where
    aux (App (Id ty) [Var _]) = do
      m <- get
      let n = Map.findWithDefault 0 ty m
      put $! Map.insert ty (n+if isDictionary ty then 0 else 1) m
      return (fun (toFun (Id ty)) [var (MkVar n)])
    aux (Fun f xs) = fmap (fun f) (mapM aux (fromTermList xs))

-- | Take a term and unify all type variables,
-- and then all variables of the same type.
-- For example, the skeleton of @x + (y + z)@
-- is @x + (x + x)@.
skeleton :: Term Constant -> Term Constant
skeleton = unifyTermVars . unifyTypeVars
  where
    unifyTypeVars = typeSubst (const (var (MkVar 0)))
    unifyTermVars = subst (const (var (MkVar 0)))

typedSubst ::
  (Symbolic a, ConstantOf a ~ Constant) =>
  (Type -> Var -> Builder Constant) -> a -> a
typedSubst sub x = replace aux x
  where
    aux Empty = mempty
    aux (Cons (App (Id ty) [Var x]) ts) = sub ty x `mappend` aux ts
    aux (Cons (Fun f ts) us) = fun f (aux ts) `mappend` aux us

typedVars :: Term Constant -> [(Type, Var)]
typedVars t = [(ty, x) | App (Id ty) [Var x] <- subterms t]

evaluateTm :: Applicative f => (Value f -> Value f) -> (Type -> Var -> Value f) -> Term Constant -> Value f
evaluateTm def env (App (Id ty) [Var v]) = def (env ty v)
evaluateTm def env (App (Apply _) [t, u]) =
  apply (evaluateTm def env t) (evaluateTm def env u)
evaluateTm def env (App f xs) =
  foldl apply x (map (evaluateTm def env) xs)
  where
    x = def (mapValue (pure . runIdentity) (conValue f))

instance CoArbitrary Var where
  coarbitrary (MkVar x) = coarbitrary x

makeValuation :: (Type -> Value Gen) -> QCGen -> Int -> Type -> Var -> Value Identity
makeValuation env g n ty x =
  mapValue (\gen -> Identity (unGen (coarbitrary (ty, x) gen) g n)) (env ty)

isOp :: String -> Bool
isOp "[]" = False
isOp ('"':_) = False
isOp xs | all (== '.') xs = True
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_' || x == '.'

constant :: Typeable a => String -> a -> Constant
constant name x = Constant name value (poly value) 0 style 1 False
  where
    value = toValue (Identity x)
    ar = typeArity (typeOf x)
    style
      | name == "()" = curried
      | take 1 name == "," = fixedArity (length name+1) tupleStyle
      | take 2 name == "(," = fixedArity (length name-1) tupleStyle
      | isOp name && ar >= 2 = infixStyle 5
      | isOp name = prefix
      | otherwise = curried
