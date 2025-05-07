{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
module QuickSpec.Internal.Haskell where

import QuickSpec.Internal.Haskell.Resolve
import QuickSpec.Internal.Type
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Pruning
import Test.QuickCheck hiding (total, classify, subterms, Fun)
import Data.Constraint hiding ((\\))
import Data.Proxy
import qualified Twee.Base as Twee
import QuickSpec.Internal.Term
import Data.Functor.Identity
import Data.Maybe
import Data.MemoUgly
import Test.QuickCheck.Gen.Unsafe
import Data.Char
import Data.Ord
import QuickSpec.Internal.Testing
import qualified QuickSpec.Internal.Testing.QuickCheck as QuickCheck
import qualified QuickSpec.Internal.Pruning.Twee as Twee
import QuickSpec.Internal.Explore hiding (quickSpec)
import qualified QuickSpec.Internal.Explore
import QuickSpec.Internal.Explore.Polymorphic(Universe(..), VariableUse(..))
import QuickSpec.Internal.Pruning.Background(Background)
import Control.Monad
import Control.Monad.Trans.State.Strict
import QuickSpec.Internal.Terminal
import Text.Printf
import QuickSpec.Internal.Utils
import Data.Lens.Light
import GHC.TypeLits
import QuickSpec.Internal.Explore.Conditionals hiding (Normal)
import Control.Spoon
import qualified Data.Set as Set
import qualified Test.QuickCheck.Poly as Poly
import Numeric.Natural(Natural)
import Test.QuickCheck.Instances()
import Data.Word
import Data.List.NonEmpty (NonEmpty)
import Data.Complex
import Data.Ratio
import Data.Functor.Compose
import Data.Int
import Data.Void
import Data.Unique
import qualified Data.Monoid as DM
import qualified Data.Semigroup as DS
import qualified Data.Map.Strict as Map
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Data.IORef
import Control.Monad.IO.Class
import Control.Exception
import QuickSpec.Internal.Parse
import Text.ParserCombinators.ReadP(ReadP, string)

baseInstances :: Instances
baseInstances =
  mconcat [
    -- Generate tuple values (pairs and () are built into findInstance)
    inst $ \(x :: A) (y :: B) (z :: C) -> (x, y, z),
    inst $ \(x :: A) (y :: B) (z :: C) (w :: D) -> (x, y, z, w),
    inst $ \(x :: A) (y :: B) (z :: C) (w :: D) (v :: E) -> (x, y, z, w, v),
    -- Split conjunctions of typeclasses into individuals
    inst $ \() -> Dict :: Dict (),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) -> Dict :: Dict (ClassA, ClassB),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) (Dict :: Dict ClassC) -> Dict :: Dict (ClassA, ClassB, ClassC),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) (Dict :: Dict ClassC) (Dict :: Dict ClassD) -> Dict :: Dict (ClassA, ClassB, ClassC, ClassD),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) (Dict :: Dict ClassC) (Dict :: Dict ClassD) (Dict :: Dict ClassE) -> Dict :: Dict (ClassA, ClassB, ClassC, ClassD, ClassE),
    inst $ \(Dict :: Dict ClassA) (Dict :: Dict ClassB) (Dict :: Dict ClassC) (Dict :: Dict ClassD) (Dict :: Dict ClassE) (Dict :: Dict ClassF) -> Dict :: Dict (ClassA, ClassB, ClassC, ClassD, ClassE, ClassF),
    -- Derive typeclass instances using (:-)
    -- N.B. flip is there to resolve (:-) first to reduce backtracking
    inst $ flip $ \(Dict :: Dict ClassA) (Sub Dict :: ClassA :- ClassB) -> Dict :: Dict ClassB,
    -- Standard names
    inst $ \(Names names :: Names A) ->
      Names (map (++ "s") names) :: Names [A],
    inst (Names ["p", "q", "r"] :: Names (A -> Bool)),
    inst (Names ["f", "g", "h"] :: Names (A -> B)),
    inst (Names ["dict"] :: Names (Dict ClassA)),
    inst (Names ["x", "y", "z", "w"] :: Names A),
    -- Allow up to 4 variables per type by default
    inst (Use (UpTo 4) :: Use A),
    -- Standard instances
    baseType (Proxy :: Proxy ()),
    baseType (Proxy :: Proxy Int),
    baseType (Proxy :: Proxy Integer),
    baseType (Proxy :: Proxy Natural),
    baseType (Proxy :: Proxy Bool),
    baseType (Proxy :: Proxy Char),
    baseType (Proxy :: Proxy Poly.OrdA),
    baseType (Proxy :: Proxy Poly.OrdB),
    baseType (Proxy :: Proxy Poly.OrdC),
    inst (Sub Dict :: () :- CoArbitrary ()),
    inst (Sub Dict :: () :- CoArbitrary Int),
    inst (Sub Dict :: () :- CoArbitrary Integer),
    inst (Sub Dict :: () :- CoArbitrary Natural),
    inst (Sub Dict :: () :- CoArbitrary Bool),
    inst (Sub Dict :: () :- CoArbitrary Char),
    inst (Sub Dict :: () :- CoArbitrary Poly.OrdA),
    inst (Sub Dict :: () :- CoArbitrary Poly.OrdB),
    inst (Sub Dict :: () :- CoArbitrary Poly.OrdC),
    inst (Sub Dict :: Eq A :- Eq [A]),
    inst (Sub Dict :: Ord A :- Ord [A]),
    inst (Sub Dict :: Arbitrary A :- Arbitrary [A]),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary [A]),
    inst (Sub Dict :: Eq A :- Eq (Maybe A)),
    inst (Sub Dict :: Ord A :- Ord (Maybe A)),
    inst (Sub Dict :: Arbitrary A :- Arbitrary (Maybe A)),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary (Maybe A)),
    inst (Sub Dict :: (Eq A, Eq B) :- Eq (Either A B)),
    inst (Sub Dict :: (Ord A, Ord B) :- Ord (Either A B)),
    inst (Sub Dict :: (Arbitrary A, Arbitrary B) :- Arbitrary (Either A B)),
    inst (Sub Dict :: (CoArbitrary A, CoArbitrary B) :- CoArbitrary (Either A B)),
    inst (Sub Dict :: (Eq A, Eq B) :- Eq (A, B)),
    inst (Sub Dict :: (Ord A, Ord B) :- Ord (A, B)),
    inst (Sub Dict :: (Arbitrary A, Arbitrary B) :- Arbitrary (A, B)),
    inst (Sub Dict :: (CoArbitrary A, CoArbitrary B) :- CoArbitrary (A, B)),
    inst (Sub Dict :: (Eq A, Eq B, Eq C) :- Eq (A, B, C)),
    inst (Sub Dict :: (Ord A, Ord B, Ord C) :- Ord (A, B, C)),
    inst (Sub Dict :: (Arbitrary A, Arbitrary B, Arbitrary C) :- Arbitrary (A, B, C)),
    inst (Sub Dict :: (CoArbitrary A, CoArbitrary B, CoArbitrary C) :- CoArbitrary (A, B, C)),
    inst (Sub Dict :: (Eq A, Eq B, Eq C, Eq D) :- Eq (A, B, C, D)),
    inst (Sub Dict :: (Ord A, Ord B, Ord C, Ord D) :- Ord (A, B, C, D)),
    inst (Sub Dict :: (Arbitrary A, Arbitrary B, Arbitrary C, Arbitrary D) :- Arbitrary (A, B, C, D)),
    inst (Sub Dict :: (CoArbitrary A, CoArbitrary B, CoArbitrary C, CoArbitrary D) :- CoArbitrary (A, B, C, D)),
    inst (Sub Dict :: (CoArbitrary A, Arbitrary B) :- Arbitrary (A -> B)),
    inst (Sub Dict :: (Arbitrary A, CoArbitrary B) :- CoArbitrary (A -> B)),
    inst (Sub Dict :: Ord A :- Eq A),
    -- From Arbitrary to Gen
    inst $ \(Dict :: Dict (Arbitrary A)) -> arbitrary :: Gen A,
    -- Observation functions
    inst $ \(Dict :: Dict (Ord A)) -> OrdInstance :: OrdInstance A,
    inst (\(Dict :: Dict (Observe A B C)) -> observeObs :: ObserveData C B),
    inst (\(Dict :: Dict (Ord A)) -> observeOrd :: ObserveData A A),
    inst (\(Dict :: Dict (Arbitrary A)) (obs :: ObserveData B C) -> observeFunction obs :: ObserveData (A -> B) C),
    inst (\(obs :: ObserveData A B) -> WrappedObserveData (toValue obs)),
    -- No warnings for TestCaseWrapped
    inst (NoWarnings :: NoWarnings (TestCaseWrapped SymA A)),
    -- Needed for typeclass-polymorphic predicates to work currently
    inst (\(Dict :: Dict ClassA) -> Dict :: Dict (Arbitrary (Dict ClassA)))]

data OrdInstance a where
  OrdInstance :: Ord a => OrdInstance a

-- A token used in the instance list for types that shouldn't generate warnings
data NoWarnings a = NoWarnings

data Use a = Use VariableUse

instance c => Arbitrary (Dict c) where
  arbitrary = return Dict

-- | A typeclass for types which support observational equality, typically used
-- for types that have no `Ord` instance.
--
-- An instance @Observe test outcome a@ declares that values of type @a@ can be
-- /tested/ for equality by random testing. You supply a function
-- @observe :: test -> outcome -> a@. Then, two values @x@ and @y@ are considered
-- equal, if for many random values of type @test@, @observe test x == observe test y@.
--
-- The function `QuickSpec.monoTypeObserve` declares a monomorphic
-- type with an observation function. For polymorphic types, use
-- `QuickSpec.inst` to declare the `Observe` instance.
--
-- For an example of using observational equality, see @<https://github.com/nick8325/quickspec/tree/master/examples/PrettyPrinting.hs PrettyPrinting.hs>@.
class (Arbitrary test, Ord outcome) => Observe test outcome a | a -> test outcome where
  -- | Make an observation on a value. Should satisfy the following law: if
  -- @x /= y@, then there exists a value of @test@ such that @observe test x /= observe test y@.
  observe :: test -> a -> outcome

  default observe :: (test ~ (), outcome ~ a) => test -> a -> outcome
  observe _ x = x

instance (Arbitrary a, Observe test outcome b) => Observe (a, test) outcome (a -> b) where
  observe (x, obs) f = observe obs (f x)

instance Observe () Int Int
instance Observe () Int8 Int8
instance Observe () Int16 Int16
instance Observe () Int32 Int32
instance Observe () Int64 Int64
instance Observe () Float Float
instance Observe () Double Double
instance Observe () Word Word
instance Observe () Word8 Word8
instance Observe () Word16 Word16
instance Observe () Word32 Word32
instance Observe () Word64 Word64
instance Observe () Integer Integer
instance Observe () Char Char
instance Observe () Bool Bool
instance Observe () Ordering Ordering
instance Observe () Void Void
instance Observe () Unique Unique
instance Observe () Natural Natural
instance Observe () DS.All DS.All
instance Observe () DS.Any DS.Any
instance Observe () () ()
instance (Observe xt xo x, Observe yt yo y)
      => Observe (xt, yt) (xo, yo) (x, y) where
  observe (xt, yt) (x, y)
    = (observe xt x, observe yt y)
instance (Observe xt xo x, Observe yt yo y, Observe zt zo z)
      => Observe (xt, yt, zt) (xo, yo, zo) (x, y, z) where
  observe (xt, yt, zt) (x, y, z)
    = (observe xt x, observe yt y, observe zt z)
instance (Observe xt xo x, Observe yt yo y, Observe zt zo z, Observe wt wo w)
      => Observe (xt, yt, zt, wt) (xo, yo, zo, wo) (x, y, z, w) where
  observe (xt, yt, zt, wt) (x, y, z, w)
    = (observe xt x, observe yt y, observe zt z, observe wt w)
instance Observe t p a => Observe t [p] [a] where
  observe t ps = fmap (observe t) ps
instance Observe t p a => Observe t (NonEmpty p) (NonEmpty a) where
  observe t ps = fmap (observe t) ps
instance Observe t p a => Observe (t, t) (p, p) (Complex a) where
  observe (t1, t2) (p1 :+ p2) = (observe t1 p1, observe t2 p2)
instance Observe t p a => Observe (t, t) (p, p) (Ratio a) where
  observe (t1, t2) (p)
    = (observe t1 $ numerator p, observe t2 $ denominator p)
instance Observe t p a => Observe t p (Identity a) where
  observe t = observe t . runIdentity
instance Observe t p (f (g a)) => Observe t p (Compose f g a) where
  observe t = observe t . getCompose
instance (Observe at ao a, Observe bt bo b)
      => Observe (at, bt) (Either ao bo) (Either a b) where
  observe (at, _) (Left a)  = Left $ observe at a
  observe (_, bt) (Right b) = Right $ observe bt b
instance Observe t p a => Observe t p (DS.Sum a) where
  observe t = observe t . DS.getSum
instance Observe t p a => Observe t p (DS.Product a) where
  observe t = observe t . DS.getProduct
instance Observe t p a => Observe t p (DS.First a) where
  observe t = observe t . DS.getFirst
instance Observe t p a => Observe t p (DS.Last a) where
  observe t = observe t . DS.getLast
instance Observe t p a => Observe t p (DS.Dual a) where
  observe t = observe t . DS.getDual
instance Observe t p a => Observe t p (DS.Min a) where
  observe t = observe t . DS.getMin
instance Observe t p a => Observe t p (DS.Max a) where
  observe t = observe t . DS.getMax
instance Observe t p a => Observe t p (DS.WrappedMonoid a) where
  observe t = observe t . DS.unwrapMonoid
instance Observe t p (f a) => Observe t p (DM.Alt f a) where
  observe t = observe t . DM.getAlt
instance Observe t p (f a) => Observe t p (DM.Ap f a) where
  observe t = observe t . DM.getAp
instance Observe t p a => Observe t (Maybe p) (DM.First a) where
  observe t = observe t . DM.getFirst
instance Observe t p a => Observe t (Maybe p) (DM.Last a) where
  observe t = observe t . DM.getLast
#if !MIN_VERSION_base(4,16,0)
instance Observe t p a => Observe t (Maybe p) (DS.Option a) where
  observe t = observe t . DS.getOption
#endif
instance Observe t p a => Observe t (Maybe p) (Maybe a) where
  observe t (Just a) = Just $ observe t a
  observe _ Nothing  = Nothing
instance (Arbitrary a, Observe t p a) => Observe (a, t) p (DS.Endo a) where
  observe t = observe t . DS.appEndo


-- | Like 'Test.QuickCheck.===', but using the 'Observe' typeclass instead of 'Eq'.
(=~=) :: (Show test, Show outcome, Observe test outcome a) => a -> a -> Property
a =~= b = property $ \test -> observe test a Test.QuickCheck.=== observe test b
infix 4 =~=

-- An observation function along with instances.
-- The parameters are in this order so that we can use findInstance to get at appropriate Wrappers.
data ObserveData a outcome where
  ObserveData :: (Arbitrary test, Ord outcome) => (test -> a -> outcome) -> ObserveData a outcome
newtype WrappedObserveData a = WrappedObserveData (Value (ObserveData a))

observeOrd :: Ord a => ObserveData a a
observeOrd = ObserveData (\() x -> x)

observeFunction :: Arbitrary a => ObserveData b outcome -> ObserveData (a -> b) outcome
observeFunction (ObserveData obs) =
  ObserveData (\(x, test) f -> obs test (f x))

observeObs :: Observe test outcome a => ObserveData a outcome
observeObs = ObserveData observe

baseType :: forall proxy a. (Ord a, Arbitrary a, Typeable a) => proxy a -> Instances
baseType _ =
  mconcat [
    inst (Dict :: Dict (Ord a)),
    inst (Dict :: Dict (Arbitrary a))]

-- Declares what variable names should be used for values of a particular type.
newtype Names a = Names { getNames :: [String] }

names :: Instances -> Type -> [String]
names insts ty =
  case findInstance insts (skolemiseTypeVars ty) of
    Just x  -> ofValue getNames x
    Nothing -> error "don't know how to name variables"

-- An Ordy a represents a value of type a together with its Ord instance.
-- A Value Ordy is a value of unknown type which implements Ord.
data Ordy a where Ordy :: Ord a => a -> Ordy a
instance Eq (Value Ordy) where x == y = compare x y == EQ

instance Ord (Value Ordy) where
  compare x y =
    case unwrap x of
      Ordy xv `In` w ->
        let Ordy yv = reunwrap w y in
        compare xv yv

-- | A test case is everything you need to evaluate a Haskell term.
data TestCase =
  TestCase {
    -- | Evaluate a variable. Returns @Nothing@ if no `Arbitrary` instance was found.
    tc_eval_var :: Var -> Maybe (Value Identity),
    -- | Apply an observation function to get a value implementing `Ord`.
    -- Returns @Nothing@ if no observer was found.
    tc_test_result :: Value Identity -> Maybe (Value Ordy) }

-- | Generate a random test case.
arbitraryTestCase :: Type -> Instances -> Gen TestCase
arbitraryTestCase def insts =
  TestCase <$> arbitraryValuation def insts <*> arbitraryObserver def insts

-- | Generate a random variable valuation.
arbitraryValuation :: Type -> Instances -> Gen (Var -> Maybe (Value Identity))
arbitraryValuation def insts = do
  memo <$> arbitraryFunction (sequence . findGenerator def insts . var_ty)

-- | Generate a random observation.
arbitraryObserver :: Type -> Instances -> Gen (Value Identity -> Maybe (Value Ordy))
arbitraryObserver def insts = do
  find <- arbitraryFunction $ sequence . findObserver insts
  return $ \x -> do
    obs <- find (defaultTo def (typ x))
    return (obs x)

findGenerator :: Type -> Instances -> Type -> Maybe (Gen (Value Identity))
findGenerator def insts ty =
  bringFunctor <$> (findInstance insts (defaultTo def ty) :: Maybe (Value Gen))

findOrdInstance :: Instances -> Type -> Maybe (Value OrdInstance)
findOrdInstance insts ty = findInstance insts ty

findObserver :: Instances -> Type -> Maybe (Gen (Value Identity -> Value Ordy))
findObserver insts ty = do
  inst <- findInstance insts ty :: Maybe (Value WrappedObserveData)
  return $
    case unwrap inst of
      WrappedObserveData val `In` valueWrapper ->
        case unwrap val of
          -- This brings Arbitrary and Ord instances into scope
          ObserveData obs `In` outcomeWrapper -> do
            test <- arbitrary
            return $ \x ->
              let value = runIdentity (reunwrap valueWrapper x)
                  outcome = obs test value
              in wrap outcomeWrapper (Ordy outcome)

-- | Generate a random function. Should be in QuickCheck.
arbitraryFunction :: CoArbitrary a => (a -> Gen b) -> Gen (a -> b)
arbitraryFunction gen = promote (\x -> coarbitrary x (gen x))

-- | Evaluate a Haskell term in an environment.
evalHaskell :: Type -> Instances -> TestCase -> Term Constant -> Maybe (Value Ordy)
evalHaskell def insts (TestCase env obs) t = do
  let eval env t = evalTerm env (evalConstant insts) t
  Identity val `In` w <- unwrap <$> eval env (defaultTo def t)
  res <- obs (wrap w (Identity val))
  -- Don't allow partial results to enter the decision tree
  guard (withValue res (\(Ordy x) -> isJust (teaspoon (x == x))))
  return res

data Constant =
  Constant {
    con_name  :: String,
    con_style :: TermStyle,
    con_value :: Value Identity,
    con_type :: Type,
    con_constraints :: [Type],
    con_size :: Int,
    con_classify :: Classification Constant,
    con_is_hole :: Bool }

instance Eq Constant where
  x == y =
    con_name x == con_name y && typ (con_value x) == typ (con_value y)

instance Ord Constant where
  compare =
    comparing $ \con ->
      (typeArity (typ con), typ con, con_name con)

instance Background Constant

con :: Typeable a => String -> a -> Constant
con name val =
  constant' name (toValue (Identity val))

constant' :: String -> Value Identity -> Constant
constant' name val =
  Constant {
    con_name = name,
    con_style =
      case () of
        _ | name == "()" -> curried
          | take 1 name == "," -> fixedArity (length name+1) tupleStyle
          | take 2 name == "(," -> fixedArity (length name-1) tupleStyle
          | isOp name && typeArity (typ val) >= 2 -> infixStyle 5
          | isOp name -> prefix
          | otherwise -> curried,
    con_value = val,
    con_type = ty,
    con_constraints = constraints,
    con_size = 1,
    con_classify = Function,
    con_is_hole = False }
  where
    (constraints, ty) = splitConstrainedType (typ val)

isOp :: String -> Bool
isOp "[]" = False
isOp ('"':_) = False
isOp xs | all (== '.') xs = True
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_' || x == '.'

-- Get selectors of a predicate
selectors :: Constant -> [Constant]
selectors con =
  case con_classify con of
    Predicate{..} -> clas_selectors
    _ -> []

-- Move the constraints of a constant back into the main type
unhideConstraint :: Constant -> Constant
unhideConstraint con =
  con {
    con_type = typ (con_value con),
    con_constraints = [] }

instance Typed Constant where
  typ = con_type
  otherTypesDL con =
    return (typ (con_value con)) `mplus`
    case con_classify con of
      Predicate{..} ->
        -- Don't call typesDL on clas_selectors because it in turn
        -- contains a reference to the predicate
        typesDL (map con_value clas_selectors) `mplus` typesDL clas_test_case `mplus` typesDL clas_true
      Selector{..} ->
        typesDL clas_pred `mplus` typesDL clas_test_case
      Function -> mzero
  typeSubst_ sub con =
    con { con_value = typeSubst_ sub (con_value con),
          con_type = typeSubst_ sub (con_type con),
          con_constraints = map (typeSubst_ sub) (con_constraints con),
          con_classify = fmap (typeSubst_ sub) (con_classify con) }

instance Pretty Constant where
  pPrint = text . con_name

instance PrettyTerm Constant where
  termStyle = con_style

instance Sized Constant where
  size = con_size
  sizeMode _ = AddArgs

instance Predicate Constant where
  classify = con_classify

evalConstant :: Instances -> Constant -> Maybe (Value Identity)
evalConstant insts Constant{..} = foldM app con_value con_constraints
  where
    app val constraint = do
      dict <- findValue insts constraint
      return (apply val dict)

class Predicateable a where
  -- A test case for predicates of type a
  -- if `a ~ A -> B -> C -> Bool` we get `TestCase a ~ (A, (B, (C, ())))`
  --
  -- Some speedup should be possible by using unboxed tuples instead...
  type PredicateTestCase a
  type PredicateResult a
  uncrry :: a -> PredicateTestCase a -> PredicateResult a
  true :: proxy a -> Constant

instance Predicateable Bool where
  type PredicateTestCase Bool = ()
  type PredicateResult Bool = Bool
  uncrry = const
  true _ = con "True" True

instance forall a b. (Predicateable b, Typeable a) => Predicateable (a -> b) where
  type PredicateTestCase (a -> b) = (a, PredicateTestCase b)
  type PredicateResult (a -> b) = PredicateResult b
  uncrry f (a, b) = uncrry (f a) b
  true _ = true (Proxy :: Proxy b)

-- A more user-friendly type for PredicateTestCase.
type FriendlyPredicateTestCase a = Friendly (PredicateTestCase a)
class HasFriendly a where
  type Friendly a
  unfriendly :: Friendly a -> a
instance HasFriendly () where
  type Friendly () = ()
  unfriendly () = ()
instance HasFriendly (a, ()) where
  type Friendly (a, ()) = a
  unfriendly a = (a, ())
instance HasFriendly (a, (b, ())) where
  type Friendly (a, (b, ())) = (a, b)
  unfriendly (a, b) = (a, (b, ()))
instance HasFriendly (a, (b, (c, ()))) where
  type Friendly (a, (b, (c, ()))) = (a, b, c)
  unfriendly (a, b, c) = (a, (b, (c, ())))
instance HasFriendly (a, (b, (c, (d, ())))) where
  type Friendly (a, (b, (c, (d, ())))) = (a, b, c, d)
  unfriendly (a, b, c, d) = (a, (b, (c, (d, ()))))

data TestCaseWrapped (t :: Symbol) a = TestCaseWrapped { unTestCaseWrapped :: a }

unfriendlyPredicateGen :: forall a b. ( Predicateable a
                       , Typeable a
                       , Typeable b
                       , Typeable (PredicateTestCase a))
                       => String -> a -> (b -> Gen (PredicateTestCase a)) -> (Instances, Constant)
unfriendlyPredicateGen name pred gen =
  let
    -- The following doesn't compile on GHC 7.10:
    -- ty = typeRep (Proxy :: Proxy (TestCaseWrapped sym (PredicateTestCase a)))
    -- (where sym was created using someSymbolVal)
    -- So do it by hand instead:
    ty = addName (typeRep (Proxy :: Proxy (TestCaseWrapped SymA (PredicateTestCase a))))

    -- Replaces SymA with 'String name'
    -- (XXX: not correct if the type 'a' also contains SymA)
    addName :: forall a. Typed a => a -> a
    addName = typeSubst sub
      where
        sub x
          | Twee.build (Twee.var x) == typeRep (Proxy :: Proxy SymA) =
            Twee.builder (typeFromTyCon (String name))
          | otherwise = Twee.var x

    instances =
      mconcat $ map (valueInst . addName)
        [toValue (Identity inst1), toValue (Identity inst2)]

    inst1 :: b -> Gen (TestCaseWrapped SymA (PredicateTestCase a))
    inst1 x = TestCaseWrapped <$> gen x

    inst2 :: Names (TestCaseWrapped SymA (PredicateTestCase a))
    inst2 = Names [name ++ "_var"]

    conPred = (con name pred) { con_classify = Predicate conSels ty (Fun (true (Proxy :: Proxy a))) }
    conSels = [ (constant' (name ++ "_" ++ show i) (select (i + length (con_constraints conPred)))) { con_classify = Selector i conPred ty, con_size = 0 } | i <- [0..typeArity (typ conPred)-1] ]

    select i =
      fromJust (cast (arrowType [ty] (typeArgs (typeOf pred) !! i)) (unPoly (compose (sel i) unwrapV)))
      where
        compose f g = apply (apply cmpV f) g
        sel 0 = fstV
        sel n = compose (sel (n-1)) sndV
        fstV = toPolyValue (fst :: (A, B) -> A)
        sndV = toPolyValue (snd :: (A, B) -> B)
        cmpV = toPolyValue ((.) :: (B -> C) -> (A -> B) -> A -> C)
        unwrapV = toPolyValue (unTestCaseWrapped :: TestCaseWrapped SymA A -> A)
  in
    (instances, conPred)

-- | Declare a predicate with a given name and value.
-- The predicate should have type @... -> Bool@.
-- Uses an explicit generator.
predicateGen :: forall a. ( Predicateable a
             , Typeable a
             , Typeable (PredicateTestCase a)
             , HasFriendly (PredicateTestCase a))
             => String -> a -> (Gen (FriendlyPredicateTestCase a)) -> (Instances, Constant)
predicateGen name pred gen =
  unfriendlyPredicateGen name pred (\() -> unfriendly <$> gen)

-- | Declare a predicate with a given name and value.
-- The predicate should have type @... -> Bool@.
predicate :: forall a. ( Predicateable a
          , PredicateResult a ~ Bool
          , Typeable a
          , Typeable (PredicateTestCase a))
          => String -> a -> (Instances, Constant)
predicate name pred = unfriendlyPredicateGen name pred inst
  where
    inst :: Dict (Arbitrary (PredicateTestCase a)) -> Gen (PredicateTestCase a)
    inst Dict = arbitrary `suchThat` uncrry pred

-- | How QuickSpec should style equations.
data PrintStyle
  = ForHumans
  | ForQuickCheck
  deriving (Eq, Ord, Show, Read, Bounded, Enum)

data Config =
  Config {
    cfg_quickCheck :: QuickCheck.Config,
    cfg_twee :: Twee.Config,
    cfg_max_size :: Int,
    cfg_max_depth :: Int,
    cfg_max_commutative_size :: Int,
    cfg_max_functions :: Int,
    cfg_instances :: Instances,
    -- This represents the constants for a series of runs of QuickSpec.
    -- Each index in cfg_constants represents one run of QuickSpec.
    -- head cfg_constants contains all the background functions.
    cfg_constants :: [[Constant]],
    cfg_default_to :: Type,
    cfg_infer_instance_types :: Bool,
    cfg_background :: [Prop (Term Constant)],
    cfg_background_str :: [String],
    cfg_print_filter :: Prop (Term Constant) -> Bool,
    cfg_print_style :: PrintStyle,
    cfg_check_consistency :: Bool,
    cfg_handle_resource_limit :: Bool
    }

lens_quickCheck = lens cfg_quickCheck (\x y -> y { cfg_quickCheck = x })
lens_twee = lens cfg_twee (\x y -> y { cfg_twee = x })
lens_max_size = lens cfg_max_size (\x y -> y { cfg_max_size = x })
lens_max_depth = lens cfg_max_depth (\x y -> y { cfg_max_depth = x })
lens_max_commutative_size = lens cfg_max_commutative_size (\x y -> y { cfg_max_commutative_size = x })
lens_max_functions = lens cfg_max_functions (\x y -> y { cfg_max_functions = x })
lens_instances = lens cfg_instances (\x y -> y { cfg_instances = x })
lens_constants = lens cfg_constants (\x y -> y { cfg_constants = x })
lens_default_to = lens cfg_default_to (\x y -> y { cfg_default_to = x })
lens_infer_instance_types = lens cfg_infer_instance_types (\x y -> y { cfg_infer_instance_types = x })
lens_background = lens cfg_background (\x y -> y { cfg_background = x })
lens_background_str = lens cfg_background_str (\x y -> y { cfg_background_str = x })
lens_print_filter = lens cfg_print_filter (\x y -> y { cfg_print_filter = x })
lens_print_style = lens cfg_print_style (\x y -> y { cfg_print_style = x })
lens_check_consistency = lens cfg_check_consistency (\x y -> y { cfg_check_consistency = x })
lens_handle_resource_limit = lens cfg_handle_resource_limit (\x y -> y { cfg_handle_resource_limit = x })

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_quickCheck = QuickCheck.Config { QuickCheck.cfg_num_tests = 1000, QuickCheck.cfg_max_test_size = 100, QuickCheck.cfg_fixed_seed = Nothing },
    cfg_twee = Twee.Config { Twee.cfg_max_term_size = minBound, Twee.cfg_max_cp_depth = maxBound },
    cfg_max_size = 7,
    cfg_max_depth = maxBound,
    cfg_max_commutative_size = 5,
    cfg_max_functions = maxBound,
    cfg_instances = mempty,
    cfg_constants = [],
    cfg_default_to = typeRep (Proxy :: Proxy Int),
    cfg_infer_instance_types = False,
    cfg_background = [],
    cfg_background_str = [],
    cfg_print_filter = \_ -> True,
    cfg_print_style = ForHumans,
    cfg_check_consistency = False,
    cfg_handle_resource_limit = False }

-- Extra types for the universe that come from in-scope instances.
instanceTypes :: Instances -> Config -> [Type]
instanceTypes insts Config{..}
  | not cfg_infer_instance_types = []
  | otherwise =
    [ tv
    | cls <- dicts,
      inst <- groundInstances,
      sub <- maybeToList (matchType cls inst),
      (_, tv) <- Twee.substToList sub ]
  where
    dicts =
      concatMap con_constraints (concat cfg_constants) >>=
      maybeToList . getDictionary

    groundInstances :: [Type]
    groundInstances =
      [ dict
      | -- () :- dict
        Twee.App tc (Twee.Cons (Twee.App unit Twee.Empty) (Twee.Cons dict Twee.Empty)) <-
        map (typeRes . typ) (is_instances insts),
        Twee.fun_value tc == tyCon (Proxy :: Proxy (:-)),
        Twee.fun_value unit == tyCon (Proxy :: Proxy (() :: Constraint)),
        Twee.isGround dict ]

data Warnings =
  Warnings {
    warn_no_generator :: [Type],
    warn_no_observer :: [Type] }

warnings :: Universe -> Instances -> Config -> Warnings
warnings univ insts Config{..} =
  Warnings {
    warn_no_generator =
      [ ty | ty <- types, isNothing (findGenerator cfg_default_to insts ty) ],
    warn_no_observer =
      [ ty | ty <- types, isNothing (findObserver insts ty) ] }
  where
    -- Check after defaulting types to Int (or whatever it is)
    types =
      [ ty
      | ty <- defaultTo cfg_default_to . Set.toList . univ_types $ univ,
        isNothing (findInstance insts ty :: Maybe (Value NoWarnings)) ]

instance Pretty Warnings where
  pPrint Warnings{..} =
    vcat $
      [section genDoc warn_no_generator] ++
      [section obsDoc warn_no_observer] ++
      [text "" | warnings ]
    where
      warnings = not (null warn_no_generator) || not (null warn_no_observer)
      section _ [] = pPrintEmpty
      section doc xs =
        doc $$
        nest 2 (vcat (map pPrintType xs)) $$
        text ""

      genDoc =
        text "WARNING: The following types have no 'Arbitrary' instance declared." $$
        text "You will not get any variables of the following types:"

      obsDoc =
        text "WARNING: The following types have no 'Ord' or 'Observe' instance declared." $$
        text "You will not get any equations about the following types:"

quickSpec :: Config -> IO [Prop (Term Constant)]
quickSpec cfg@Config{..} = do
  propNo <- newIORef 1
  props <- newIORef ([] :: [Prop (Term Constant)])

  let
    constantsOf f =
      usort (concatMap funs $
        [clas_true | Predicate{..} <- map classify (f cfg_constants)] ++
        [clas_true (classify clas_pred) | Selector{..} <- map classify (f cfg_constants)]) ++
      f cfg_constants ++ concatMap selectors (f cfg_constants)
    constants = constantsOf concat

    univ = conditionalsUniverse (instanceTypes instances cfg) constants
    instances = cfg_instances `mappend` baseInstances

    eval = evalHaskell cfg_default_to instances
    was_observed = isNothing . findOrdInstance instances  -- it was observed if there is no Ord instance directly in scope

    prettierProp funs norm = prettyDefinition funs . prettyAC norm . conditionalise
    prettiestProp funs norm = prettyProp (names instances) . prettierProp funs norm

    present funs prop = do
      norm <- normaliser
      let prop' = prettierProp funs norm prop
      when (not (hasBackgroundPredicates prop') && not (isBackgroundProp prop') && cfg_print_filter prop) $ do
        n <- liftIO $ readIORef propNo
        liftIO $ writeIORef propNo (n+1)
        putLine $
          case cfg_print_style of
            ForHumans ->
              printf "%3d. %s" n $ show $
                prettiestProp funs norm prop <+> disambiguatePropType prop
            ForQuickCheck ->
              renderStyle (style {lineLength = 78}) $ nest 2 $
                prettyPropQC
                  cfg_default_to
                  was_observed
                  n
                  (names instances)
                  prop'
                  <+> disambiguatePropType prop

    hasBackgroundPredicates (_ :=>: t :=: u)
      | not (null [p | p <- funs t, isBackgroundPredicate p]),
        not (null [q | q <- funs u, isBackgroundPredicate q]) =
        True
    hasBackgroundPredicates _ = False
    isBackgroundPredicate p =
      p `elem` concat (take 1 cfg_constants) &&
      case classify p of
        Predicate{} -> True
        _ -> False

    isBackgroundProp p =
      not (null fs) && and [f `elem` concat (take 1 cfg_constants) | f <- fs]
      where
        fs = funs p

    -- XXX do this during testing
    constraintsOk = memo $ \con ->
      or [ and [ isJust (findValue instances (defaultTo cfg_default_to constraint)) | constraint <- con_constraints (typeSubst sub con) ]
         | ty <- Set.toList (univ_types univ),
           sub <- maybeToList (matchType (typeRes (typ con)) ty) ]

    enumerator cons =
      sortTerms measure $
      filterEnumerator (all constraintsOk . funs) $
      filterEnumerator (\t -> length (usort (funs t)) <= cfg_max_functions) $
      filterEnumerator (\t -> depth t <= cfg_max_depth) $
      filterEnumerator (\t -> size t + length (conditions t) <= cfg_max_size) $
      enumerateConstants atomic `mappend` enumerateApplications
      where
        atomic = cons ++ [Var (V typeVar 0)]

    conditions t = usort [p | f <- funs t, Selector _ p _ <- [classify f]]

    use ty =
      ofValue (\(Use x) -> x) $ fromJust $
      (findInstance instances ty :: Maybe (Value Use))

    mainOf n f g = do
      unless (null (f cfg_constants)) $ do
        putLine $ show $ pPrintSignature
          (map (Fun . unhideConstraint) (f cfg_constants))
        putLine ""
      when (n > 0) $ do
        putText (prettyShow (warnings univ instances cfg))
        putLine "== Laws =="
        when (cfg_print_style == ForQuickCheck) $ do
          putLine "quickspec_laws :: [(String, Property)]"
          putLine "quickspec_laws ="
      let
        pres prop = do
          liftIO $ modifyIORef props (prop:)
          if n == 0 then return () else present (constantsOf f) prop
      QuickSpec.Internal.Explore.quickSpec pres (flip eval) cfg_max_size cfg_max_commutative_size use univ
        (enumerator (map Fun (constantsOf g)))
      when (n > 0) $ do
        when (cfg_print_style == ForQuickCheck) $ putLine "  ]"
        putLine ""

    main = do
      forM_ cfg_background $ \prop -> do
        add prop
      forM_ cfg_background_str $ \prop_str -> do
        add (parseProp parseFun prop_str)

      mapM_ round [0..rounds-1]
      where
        round n = mainOf n (concat . take 1 . drop n) (concat . take (n+1))
        rounds = length cfg_constants

    -- Used in adding background functions from strings
    parseFun :: ReadP Constant
    parseFun = msum [do { string (con_name c); return c } | c <- constants ]

    -- Used in checkConsistency. Generate a term to be used when a
    -- Twee proof contains a hole ("?"), i.e. a don't-care variable.
    hole ty = do
      -- It doesn't matter what the value of the variable is, so
      -- generate a single random value and use that.
      vgen <- findInstance instances ty :: Maybe (Value Gen)
      let runGen g = Identity (unGen g (mkQCGen 1234) 5)
      return $ Fun $ (constant' "hole" (mapValue runGen vgen)) { con_is_hole = True }

    -- Remove holes by replacing them with a fresh variable.
    removeHoles prop = mapTerm (flatMapFun f) prop
      where
        f con
          | con_is_hole con = Var (V (typ con) n)
          | otherwise = Fun con
        n = freeVar prop

    checkConsistency = do
      thms <- theorems hole
      let numThms = length thms
      norm <- normaliser

      forM_ (zip [1 :: Int ..] thms) $ \(i, thm) -> do
        putStatus (printf "checking laws for consistency: %d/%d" i numThms)
        res <- test (prop thm)
        case res of
          TestFailed testcase -> do
            forM_ (axiomsUsed thm) $ \(ax, insts) ->
              forM_ insts $ \inst -> do
                res <- retest testcase inst
                when (testResult res == TestFailed ()) $ do
                  modify (Map.insertWith Set.union (removeHoles ax) (Set.singleton (removeHoles inst)))
          _ -> return ()

      falseProps <- get
      forM_ (Map.toList falseProps) $ \(ax, insts) -> do
        putLine (printf "*** Law %s is false!" (prettyShow (prettiestProp constants norm ax)))
        putLine "False instances:"
        forM_ (Set.toList insts) $ \inst -> do
          putLine (printf "  %s is false" (prettyShow (prettiestProp constants norm inst)))
        putLine ""

  handleJust (\ex -> if cfg_handle_resource_limit && isResourceLimitException ex then Just () else Nothing) return $
    join $
      fmap withStdioTerminal $
      generate $
      QuickCheck.run cfg_quickCheck (arbitraryTestCase cfg_default_to instances) eval $
      Twee.run cfg_twee { Twee.cfg_max_term_size = Twee.cfg_max_term_size cfg_twee `max` cfg_max_size } $
      runConditionals constants $ do
        main
        when cfg_check_consistency $ void $ execStateT checkConsistency Map.empty

  let maybeConditionalise prop
        | prop == prop' = [prop]
        | otherwise = [prop, prop']
        where prop' = conditionalise prop

  -- Return conditional properties both in conditionalised and raw form.
  -- Raw form is needed if the properties will be passed to addBackground,
  -- but conditionalised is better for other uses.
  concatMap maybeConditionalise . reverse <$> readIORef props
