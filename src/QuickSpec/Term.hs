-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor, FlexibleContexts, GADTs #-}
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
import Test.QuickCheck.Random
import Data.Ratio

-- * Terms and schemas

type TermOf = Tm Constant

-- | A term is composed of nested functions applications over free variables, e.g.:
--
-- * @x + y@
-- * @x + x@
-- * @f ((x + 0) + y)@
type Term = TermOf Variable

-- | A schema is like a term but has holes instead of variables, e.g.:
--
--   * @_ + _@
--   * @_ + (0 + _)@
--   * @f _ _@
type Schema = TermOf Hole

class Minimal a where
  minimal :: a

class Sized a where
  funSize  :: a -> Rational
  funArity :: a -> Int

type Measure f v = (Rational, Int, MeasureFuns f (), Int, [v])

-- | Measures term ordering - size, skeleton, generality.
--
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
measure :: (Sized f, Ord f, Ord v) => Tm f v -> Measure f v
measure t = (exactSize t, -length (vars t),
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
  compare f g `orElse`
  compare (map MeasureFuns ts) (map MeasureFuns us)

-- | Take two terms and find the first place where they differ.
compareTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe (Tm f v, Tm f v, Ordering)
compareTerms t u =
  here (comparing exactSize t u) `mplus`
  case (t, u) of
    (Var x, Var y) -> here (compare x y)
    (Var{}, Fun{}) -> here LT
    (Fun{}, Var{}) -> here GT
    (Fun f xs, Fun g ys) ->
      here (compare f g) `mplus`
      msum (zipWith compareTerms xs ys)
  where
    here EQ = Nothing
    here ord = Just (t, u, ord)

-- | Reduction ordering (i.e., a partial order closed under substitution).
orientTerms :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Maybe Ordering
orientTerms t u =
  case compareTerms t u of
    Just (t', u', LT) -> do { guard (check t u t' u'); return LT }
    Just (t', u', GT) -> do { guard (check u t u' t'); return GT }
    Nothing           -> Just EQ
  where
    check t u t' u' =
      sort (vars t') `isSubsequenceOf` sort (vars u') &&
      sort (vars t)  `isSubsequenceOf` sort (vars u)

simplerThan :: (Sized f, Ord f, Ord v) => Tm f v -> Tm f v -> Bool
t `simplerThan` u = orientTerms t u == Just LT

size :: Sized f => Tm f v -> Int
size t = ceiling (exactSize t)

exactSize :: Sized f => Tm f v -> Rational
exactSize (Var x) = 1
exactSize (Fun f xs) = funSize f + sum (map exactSize xs)

-- | Constants have values, while variables do not (as only monomorphic
--   variables have generators, so we need a separate defaulting phase).
data Constant =
  Constant {
    conIndex        :: Int,
    conName         :: String,
    conValue        :: Value Identity,
    conGeneralValue :: Poly (Value Identity),
    conArity        :: Int,
    conStyle        :: TermStyle,
    conSize         :: Int,
    conIsBackground :: Bool }
  deriving Show

idConstant :: Constant
idConstant =
  Constant {
    conIndex        = -1,
    conName         = "id",
    conValue        = toValue (return (id :: (A -> B) -> A -> B)),
    conGeneralValue = poly (toValue (return (id :: (A -> B) -> A -> B))),
    conArity        = 0,
    conStyle        = Invisible,
    conSize         = 0,
    conIsBackground = True }

isId :: Constant -> Bool
isId x = conIndex x == -1

idTerm :: Typed v => TermOf v -> Maybe (TermOf v)
idTerm t = do
  Fun Arrow [arg, res] <- return (typ t)
  let f (TyVar 0) = arg
      f (TyVar 1) = res
  let con = idConstant {
        conValue = typeSubst f (conValue idConstant),
        conArity = 1 }
  return (Fun con [t])

instance Eq Constant where x == y = x `compare` y == EQ
instance Ord Constant where
  compare = comparing (\c -> (isId c, twiddle (conArity c), conIndex c, typ (conValue c)))
    where
      -- This tweak is taken from Prover9
      twiddle 2 = 1
      twiddle 1 = 2
      twiddle n = n
instance Pretty Constant where
  pretty = text . conName
instance PrettyTerm Constant where
  termStyle = conStyle
  implicitArguments f =
    go (typ (conGeneralValue f))
    where
      go (Fun Arrow [t, u]) | isDictionary t = 1 + go u
      go _ = 0
instance Typed Constant where
  typ = typ . conValue
  typeSubst sub x = x { conValue = typeSubst sub (conValue x) }
instance Sized Constant where
  funSize  = fromIntegral . conSize
  funArity = conArity

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

-- | Holes - a newtype largely so that we can improve the pretty-printing.
newtype Hole = Hole Type deriving (Eq, Ord, Show, Typed)
instance Pretty Hole where pretty _ = text "_"

instance Typed v => Typed (TermOf v) where
  typ (Var x) = typ x
  typ (Fun f xs) = typeDrop (length xs) (typ f)
  otherTypesDL t = (varsDL t >>= typesDL) `mplus` (funsDL t >>= typesDL)

  typeSubst sub (Var x) = Var (typeSubst sub x)
  typeSubst sub (Fun f ts) = Fun (typeSubst sub f) (map (typeSubst sub) ts)

instance Typed v => Apply (TermOf v) where
  tryApply t@(Fun f xs) u
    | arity (typ (conGeneralValue f) ) > length xs =
        case typ t of
          Fun Arrow [arg, _] | arg == typ u -> Just (Fun f' (xs ++ [u]))
          _ -> Nothing
    where
      f' = f { conArity = conArity f + 1 }
  tryApply t u = do { t' <- idTerm t; tryApply t' u }

-- | Turn a term into a schema by forgetting about its variables.
schema :: Term -> Schema
schema = rename (Hole . typ)

-- | Instantiate a schema by making all the variables different.
instantiate :: Schema -> Term
instantiate s = evalState (aux s) Map.empty
  where
    aux (Var (Hole ty)) = do
      m <- get
      let n = Map.findWithDefault 0 ty m
      put $! Map.insert ty (n+1) m
      return (Var (Variable n ty))
    aux (Fun f xs) = fmap (Fun f) (mapM aux xs)

-- | Take a term and unify all type variables,
--   and then all variables of the same type.
--
--   The term @x + (y + z)@ becomes @x + (x + x)@
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

makeValuation :: (CoArbitrary v, Typed v) => (Type -> Value Gen) -> QCGen -> Int -> v -> Value Identity
makeValuation env g n x =
  mapValue (\gen -> Identity (unGen (coarbitrary x gen) g n)) (env (typ x))
