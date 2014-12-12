-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor #-}
module QuickSpec.Term where

#include "errors.h"
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import Data.List
import qualified Data.Map as Map
import Data.Ord
import qualified Data.Rewriting.Substitution.Type as T
import QuickSpec.Base
import QuickSpec.Type
import QuickSpec.Utils
import Test.QuickCheck
import Test.QuickCheck.Gen

-- Terms and schemas.
-- A schema is like a term but has holes instead of variables.
type TermOf = Tm Constant
type Term = TermOf Variable
type Schema = TermOf Hole

class Sized a where
  funSize :: a -> Int

-- Term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure f v = (Int, Int, MeasureFuns f (), Int, [v])
measure :: (Sized f, Ord f, Ord v) => Tm f v -> Measure f v
measure t = (size t, -length (vars t),
             MeasureFuns (rename (const ()) t), -length (usort (vars t)), vars t)

newtype MeasureFuns f v = MeasureFuns (Tm f v)
instance (Sized f, Ord f, Ord v) => Eq (MeasureFuns f v) where
  t == u = compare t u == EQ
instance (Sized f, Ord f, Ord v) => Ord (MeasureFuns f v) where
  compare (MeasureFuns t) (MeasureFuns u) = compareFuns t u

compareFuns :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Ordering
compareFuns (Var x) (Var y) = compare x y
compareFuns Var{} Fun{} = LT
compareFuns Fun{} Var{} = GT
compareFuns (Fun f ts) (Fun g us) =
  compare (f :/: length ts) (g :/: length us) `orElse`
  compare (map MeasureFuns ts) (map MeasureFuns us)

-- Take two terms and find the first place where they differ.
compareTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe (Tm f v, Tm f v, Ordering)
compareTerms t u =
  here (comparing size t u) `mplus`
  case (t, u) of
    (Var x, Var y) -> here (compare x y)
    (Var{}, Fun{}) -> here LT
    (Fun{}, Var{}) -> here GT
    (Fun f xs, Fun g ys) ->
      here (compare (f :/: length xs) (g :/: length ys)) `mplus`
      msum (zipWith compareTerms xs ys)
  where
    here EQ = Nothing
    here ord = Just (t, u, ord)

data Arity f = f :/: Int deriving (Eq, Show)

instance Ord f => Ord (Arity f) where
  compare = comparing (\(f :/: n) -> (twiddle n, f))
    where
      -- This tweak is taken from Prover9
      twiddle 2 = 1
      twiddle 1 = 2
      twiddle n = n

instance Pretty f => Pretty (Arity f) where
  pretty (f :/: n) = pretty f <> text "/" <> pretty n

-- Reduction ordering (i.e., a partial order closed under substitution).
orientTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe Ordering
orientTerms t u =
  case compareTerms t u of
    Just (t', u', LT) -> do { guard (check t u t' u'); return LT }
    Just (t', u', GT) -> do { guard (check u t u' t'); return GT }
    _                 -> Nothing
  where
    check t u t' u' =
      sort (vars t') `isSubsequenceOf` sort (vars u') &&
      sort (vars t)  `isSubsequenceOf` sort (vars u)

simplerThan :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Bool
t `simplerThan` u = orientTerms t u == Just LT

size :: Sized f => Tm f v -> Int
size (Var x) = 1
size (Fun f xs) = funSize f + sum (map size xs)

-- Constants have values, while variables do not (as only monomorphic
-- variables have generators, so we need a separate defaulting phase).
data Constant =
  Constant {
    conName         :: String,
    conValue        :: Value Identity,
    conGeneralValue :: Poly (Value Identity),
    conStyle        :: TermStyle,
    conSize         :: Int,
    conIsBackground :: Bool }
  deriving Show
instance Eq Constant where x == y = x `compare` y == EQ
instance Ord Constant where compare = comparing (\c -> (conName c, typ (conGeneralValue c)))
instance Pretty Constant where
  pretty = text . conName
instance PrettyTerm Constant where
  termStyle = conStyle
instance Typed Constant where
  typ = typ . conValue
  typeSubst sub x = x { conValue = typeSubst sub (conValue x) }
instance Sized Constant where
  funSize = conSize

-- We're not allowed to have two variables with the same number
-- but unifiable types.
data Variable =
  Variable {
    varNumber :: Int,
    varType   :: Type }
  deriving (Show, Eq, Ord)
instance Pretty Variable where
  pretty x = text (supply ["x","y","z"] !! varNumber x)
instance Typed Variable where
  typ = varType
  typeSubst sub (Variable n ty) = Variable n (typeSubst sub ty)
instance Numbered Variable where
  number = varNumber
  withNumber n x = x { varNumber = n }
instance CoArbitrary Variable where
  coarbitrary x = coarbitrary (varNumber x) . coarbitrary (varType x)

-- Holes - a newtype largely so that we can improve the pretty-printing.
newtype Hole = Hole Type deriving (Eq, Ord, Show, Typed)
instance Pretty Hole where pretty _ = text "_"

instance Typed v => Typed (TermOf v) where
  typ (Var x) = typ x
  typ (Fun f xs) = typeDrop (length xs) (typ f)
    where
      typeDrop 0 ty = ty
      typeDrop n (Fun Arrow [_, ty]) = typeDrop (n-1) ty
  otherTypesDL t = (varsDL t >>= typesDL) `mplus` (funsDL t >>= typesDL)

  typeSubst sub (Var x) = Var (typeSubst sub x)
  typeSubst sub (Fun f ts) = Fun (typeSubst sub f) (map (typeSubst sub) ts)

instance Typed v => Apply (TermOf v) where
  tryApply t@(Fun f xs) u
    | arity (typ (conGeneralValue f)) > length xs =
      case typ t of
        Fun Arrow [arg, _] | arg == typ u -> Just (Fun f (xs ++ [u]))
        _ -> Nothing
  tryApply _ _ = Nothing

-- Turn a term into a schema by forgetting about its variables.
schema :: Term -> Schema
schema = rename (Hole . typ)

-- Instantiate a schema by making all the variables different.
instantiate :: Schema -> Term
instantiate s = evalState (aux s) Map.empty
  where
    aux (Var (Hole ty)) = do
      m <- get
      let n = Map.findWithDefault 0 ty m
      put $! Map.insert ty (n+1) m
      return (Var (Variable n ty))
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

-- Take a term and unify all type variables,
-- and then all variables of the same type.
skeleton :: (Ord v, Typed v) => TermOf v -> TermOf v
skeleton = unifyTermVars . unifyTypeVars
  where
    unifyTypeVars = typeSubst (const (Var (TyVar 0)))
    unifyTermVars t = subst (T.fromMap (Map.fromList (makeSubst (vars t)))) t
    makeSubst xs =
      [ (v, Var w) | vs@(w:_) <- partitionBy typ xs, v <- vs ]

evaluateTm :: (Typed v, Applicative f, Show v) => (v -> Value f) -> Tm Constant v -> Value f
evaluateTm env (Var v) = env v
evaluateTm env (Fun f xs) =
  foldl apply x (map (evaluateTm env) xs)
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
