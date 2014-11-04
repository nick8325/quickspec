-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor #-}
module QuickSpec.Term where

#include "errors.h"
import QuickSpec.Utils
import QuickSpec.Base
import QuickSpec.Type
import Test.QuickCheck
import Test.QuickCheck.Gen
import Control.Monad.Trans.State.Strict
import Data.Ord
import qualified Data.Map as Map
import Data.Functor.Identity
import Control.Applicative
import Data.Traversable(traverse)
import qualified Data.Rewriting.Substitution.Type as T
import Data.List
import Control.Monad
import Data.Maybe

-- Terms and schemas.
-- A schema is like a term but has holes instead of variables.
type TermOf = Tm Constant
type Term = TermOf Variable
type Schema = TermOf Hole

class Sized a where
  funSize :: a -> Int
  -- Map all Skolem constants to the same constant.
  schematise :: a -> a
  schematise = id

-- Term ordering.
-- Satisfies the property:
-- if Measure (schema t) < Measure (schema u) then Measure t < Measure u.
newtype Measure f v = Measure (Tm f v)
instance (Sized f, Ord f, Ord v) => Eq (Measure f v) where
  t == u = compare t u == EQ
instance (Sized f, Ord f, Ord v) => Ord (Measure f v) where
  compare (Measure t) (Measure u) =
    compareSchema t u `orElse` comparing rest t u
    where
      -- Order instances of the same schema by generality
      -- Look at funs t too to deal with Skolem constants
      rest t = (-length (usort (vars t)), vars t,
                -length (usort (funs t)), funs t)

compareSchema :: (Sized f, Ord f) => Tm f v -> Tm f v -> Ordering
compareSchema t u =
  case compareTerms (toSchema t) (toSchema u) of
    Nothing -> EQ
    Just (_, _, ord) -> ord
  where
    toSchema = mapTerm schematise (const ())

-- Take two terms and find the first place where they differ.
compareTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe (Tm f v, Tm f v, Ordering)
compareTerms t u =
  here (comparing size t u) `mplus`
  case (t, u) of
    (Var x, Var y) -> here (compare x y)
    (Var{}, Fun{}) -> here LT
    (Fun{}, Var{}) -> here GT
    (Fun f xs, Fun g ys) ->
      -- Order constants by arity first
      here (compare (length xs) (length ys)) `mplus`
      here (compare f g) `mplus` msum (zipWith compareTerms xs ys)
  where
    here EQ = Nothing
    here ord = Just (t, u, ord)

-- Reduction ordering (i.e., a partial order closed under substitution).
-- Has the property:
-- if t `simplerThan` u then Measure (schema t) < Measure (schema u).
orientTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe Ordering
orientTerms t u =
  case compareTerms t u of
    Just (t', u', LT) -> do { guard (check t u t' u'); return LT }
    Just (t', u', GT) -> do { guard (check u t u' t'); return GT }
    Nothing           -> return EQ
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
  typeSubstA s (Constant name value generalValue pretty size isBackground) =
    Constant name <$> typeSubstA s value <*> pure generalValue <*> pure pretty <*> pure size <*> pure isBackground
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
  typeSubstA s (Variable n ty) =
    Variable n <$> typeSubstA s ty
instance CoArbitrary Variable where
  coarbitrary x = coarbitrary (varNumber x) . coarbitrary (varType x)

-- Holes - a newtype largely so that we can improve the pretty-printing.
newtype Hole = Hole Type deriving (Eq, Ord, Show)
instance Typed Hole where
  typ (Hole ty) = ty
  typeSubstA f (Hole ty) = Hole <$> typeSubstA f ty
instance Pretty Hole where pretty _ = text "_"

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
