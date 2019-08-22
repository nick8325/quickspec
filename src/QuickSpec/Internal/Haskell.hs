{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Data.List
import Data.Proxy
import qualified Twee.Base as Twee
import QuickSpec.Internal.Term
import Data.Functor.Identity
import Data.Maybe
import Data.MemoUgly
import Test.QuickCheck.Gen.Unsafe
import Data.Char
import Data.Ord
import qualified QuickSpec.Internal.Testing.QuickCheck as QuickCheck
import qualified QuickSpec.Internal.Pruning.Twee as Twee
import QuickSpec.Internal.Explore hiding (quickSpec)
import qualified QuickSpec.Internal.Explore
import QuickSpec.Internal.Explore.Polymorphic(Universe(..))
import QuickSpec.Internal.Pruning.Background(Background)
import Control.Monad
import Control.Monad.Trans.State.Strict
import QuickSpec.Internal.Terminal
import Text.Printf
import QuickSpec.Internal.Utils
import Data.Lens.Light
import GHC.TypeLits
import QuickSpec.Internal.Explore.Conditionals
import Control.Spoon
import qualified Data.Set as Set
import qualified Test.QuickCheck.Poly as Poly
import Numeric.Natural
import Test.QuickCheck.Instances()

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
    inst (\(Dict :: Dict (Observe A B C)) -> observeObs :: ObserveData C B),
    inst (\(Dict :: Dict (Ord A)) -> observeOrd :: ObserveData A A),
    inst (\(Dict :: Dict (Arbitrary A)) (obs :: ObserveData B C) -> observeFunction obs :: ObserveData (A -> B) C),
    inst (\(obs :: ObserveData A B) -> WrappedObserveData (toValue obs)),
    -- No warnings for TestCaseWrapped
    inst (NoWarnings :: NoWarnings (TestCaseWrapped SymA A)),
    -- Needed for typeclass-polymorphic predicates to work currently
    inst (\(Dict :: Dict ClassA) -> Dict :: Dict (Arbitrary (Dict ClassA)))]

-- A token used in the instance list for types that shouldn't generate warnings
data NoWarnings a = NoWarnings

data SingleUse a = SingleUse

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
evalHaskell :: Type -> Instances -> TestCase -> Term Constant -> Either (Value Ordy) (Term Constant)
evalHaskell def insts (TestCase env obs) t =
  maybe (Right t) Left $ do
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
    con_pretty_arity :: Int,
    con_value :: Value Identity,
    con_type :: Type,
    con_constraints :: [Type],
    con_size :: Int,
    con_classify :: Classification Constant }

instance Eq Constant where
  x == y =
    con_name x == con_name y && typ (con_value x) == typ (con_value y)

instance Ord Constant where
  compare =
    comparing $ \con ->
      (con_name con, twiddle (con_pretty_arity con), typ con)
      where
        -- This trick comes from Prover9 and improves the ordering somewhat
        twiddle 1 = 2
        twiddle 2 = 1
        twiddle x = x

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
    con_pretty_arity =
      case () of
        _ | isOp name && typeArity (typ val) >= 2 -> 2
          | isOp name -> 1
          | otherwise -> typeArity (typ val),
    con_value = val,
    con_type = ty,
    con_constraints = constraints,
    con_size = 1,
    con_classify = Function }
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

instance PrettyArity Constant where
  prettyArity = con_pretty_arity

instance Sized Constant where
  size = con_size

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
  uncrry :: a -> PredicateTestCase a -> Bool

instance Predicateable Bool where
  type PredicateTestCase Bool = ()
  uncrry = const

instance forall a b. (Predicateable b, Typeable a) => Predicateable (a -> b) where
  type PredicateTestCase (a -> b) = (a, PredicateTestCase b)
  uncrry f (a, b) = uncrry (f a) b

data TestCaseWrapped (t :: Symbol) a = TestCaseWrapped { unTestCaseWrapped :: a }

true :: Constant
true = con "True" True

trueTerm :: Term Constant
trueTerm = Fun true

-- | Declare a predicate with a given name and value.
-- The predicate should have type @... -> Bool@.
-- Uses an explicit generator.
predicateGen :: forall a b. ( Predicateable a
             , Typeable a
             , Typeable b
             , Typeable (PredicateTestCase a))
             => String -> a -> (b -> Gen (PredicateTestCase a)) -> (Instances, Constant)
predicateGen name pred gen =
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

    conPred = (con name pred) { con_classify = Predicate conSels ty (Fun true) }
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
predicate :: forall a. ( Predicateable a
          , Typeable a
          , Typeable (PredicateTestCase a))
          => String -> a -> (Instances, Constant)
predicate name pred = predicateGen name pred inst
  where
    inst :: Dict (Arbitrary (PredicateTestCase a)) -> Gen (PredicateTestCase a)
    inst Dict = arbitrary `suchThat` uncrry pred

data Config =
  Config {
    cfg_quickCheck :: QuickCheck.Config,
    cfg_twee :: Twee.Config,
    cfg_max_size :: Int,
    cfg_max_commutative_size :: Int,
    cfg_instances :: Instances,
    -- This represents the constants for a series of runs of QuickSpec.
    -- Each index in cfg_constants represents one run of QuickSpec.
    -- head cfg_constants contains all the background functions.
    cfg_constants :: [[Constant]],
    cfg_default_to :: Type,
    cfg_infer_instance_types :: Bool,
    cfg_background :: [Prop (Term Constant)],
    cfg_print_filter :: Prop (Term Constant) -> Bool
    }

lens_quickCheck = lens cfg_quickCheck (\x y -> y { cfg_quickCheck = x })
lens_twee = lens cfg_twee (\x y -> y { cfg_twee = x })
lens_max_size = lens cfg_max_size (\x y -> y { cfg_max_size = x })
lens_max_commutative_size = lens cfg_max_commutative_size (\x y -> y { cfg_max_commutative_size = x })
lens_instances = lens cfg_instances (\x y -> y { cfg_instances = x })
lens_constants = lens cfg_constants (\x y -> y { cfg_constants = x })
lens_default_to = lens cfg_default_to (\x y -> y { cfg_default_to = x })
lens_infer_instance_types = lens cfg_infer_instance_types (\x y -> y { cfg_infer_instance_types = x })
lens_background = lens cfg_background (\x y -> y { cfg_background = x })
lens_print_filter = lens cfg_print_filter (\x y -> y { cfg_print_filter = x })

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_quickCheck = QuickCheck.Config { QuickCheck.cfg_num_tests = 1000, QuickCheck.cfg_max_test_size = 100, QuickCheck.cfg_fixed_seed = Nothing },
    cfg_twee = Twee.Config { Twee.cfg_max_term_size = minBound, Twee.cfg_max_cp_depth = maxBound },
    cfg_max_size = 7,
    cfg_max_commutative_size = 5,
    cfg_instances = mempty,
    cfg_constants = [],
    cfg_default_to = typeRep (Proxy :: Proxy Int),
    cfg_infer_instance_types = False,
    cfg_background = [],
    cfg_print_filter = \_ -> True }

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
  let
    constantsOf f =
      [true | any (/= Function) (map classify (f cfg_constants))] ++
      f cfg_constants ++ concatMap selectors (f cfg_constants)
    constants = constantsOf concat
    
    univ = conditionalsUniverse (instanceTypes instances cfg) constants
    instances = cfg_instances `mappend` baseInstances

    eval = evalHaskell cfg_default_to instances

    present funs prop = do
      norm <- normaliser
      let prop' = makeDefinition funs (ac norm (conditionalise prop))
      when (cfg_print_filter prop) $ do
        (n :: Int, props) <- get
        put (n+1, prop':props)
        putLine $
          printf "%3d. %s" n $ show $
            prettyProp (names instances) prop' <+> maybeType prop

    -- Put an equation that defines the function f into the form f lhs = rhs.
    -- An equation defines f if:
    --   * it is of the form f lhs = rhs (or vice versa).
    --   * f is not a background function.
    --   * lhs only contains background functions.
    --   * rhs does not contain f.
    --   * all vars in rhs appear in lhs
    makeDefinition cons (lhs :=>: t :=: u)
      | Just (f, ts) <- defines u,
        f `notElem` funs t,
        null (usort (vars t) \\ vars ts) =
        lhs :=>: u :=: t
        -- In the case where t defines f, the equation is already oriented correctly
      | otherwise = lhs :=>: t :=: u
      where
        defines (Fun f :@: ts)
          | f `elem` cons,
            all (`notElem` cons) (funs ts) = Just (f, ts)
        defines _ = Nothing

    -- Transform x+(y+z) = y+(x+z) into associativity, if + is commutative
    ac norm (lhs :=>: Fun f :@: [Var x, Fun f1 :@: [Var y, Var z]] :=: Fun f2 :@: [Var y1, Fun f3 :@: [Var x1, Var z1]])
      | f == f1, f1 == f2, f2 == f3,
        x == x1, y == y1, z == z1,
        x /= y, y /= z, x /= z,
        norm (Fun f :@: [Var x, Var y]) == norm (Fun f :@: [Var y, Var x]) =
          lhs :=>: Fun f :@: [Fun f :@: [Var x, Var y], Var z] :=: Fun f :@: [Var x, Fun f :@: [Var y, Var z]]
    ac _ prop = prop

    -- Add a type signature when printing the equation x = y.
    maybeType (_ :=>: x@(Var _) :=: Var _) =
      text "::" <+> pPrintType (typ x)
    maybeType _ = pPrintEmpty

    -- XXX do this during testing
    constraintsOk = memo $ \con ->
      or [ and [ isJust (findValue instances (defaultTo cfg_default_to constraint)) | constraint <- con_constraints (typeSubst sub con) ]
         | ty <- Set.toList (univ_types univ),
           sub <- maybeToList (matchType (typeRes (typ con)) ty) ]

    enumerator cons =
      sortTerms measure $
      filterEnumerator (all constraintsOk . funs) $
      filterEnumerator (\t -> size t + length (conditions t) <= cfg_max_size) $
      enumerateConstants atomic `mappend` enumerateApplications
      where
        atomic = cons ++ [Var (V typeVar 0)]

    conditions t = usort [p | f <- funs t, Selector _ p _ <- [classify f]]

    singleUse ty =
      isJust (findInstance instances ty :: Maybe (Value SingleUse))

    mainOf n f g = do
      unless (null (f cfg_constants)) $ do
        putLine $ show $ pPrintSignature
          (map (Fun . unhideConstraint) (f cfg_constants))
        putLine ""
      when (n > 0) $ do
        putText (prettyShow (warnings univ instances cfg))
        putLine "== Laws =="
      let pres = if n == 0 then \_ -> return () else present (constantsOf f)
      QuickSpec.Internal.Explore.quickSpec pres (flip eval) cfg_max_size cfg_max_commutative_size singleUse univ
        (enumerator (map Fun (constantsOf g)))
      when (n > 0) $ do
        putLine ""

    main = do
      forM_ cfg_background $ \prop -> do
        add prop
      mapM_ round [0..rounds-1]
      where
        round n = mainOf n (concat . take 1 . drop n) (concat . take (n+1))
        rounds = length cfg_constants

  join $
    fmap withStdioTerminal $
    generate $
    QuickCheck.run cfg_quickCheck (arbitraryTestCase cfg_default_to instances) eval $
    Twee.run cfg_twee { Twee.cfg_max_term_size = Twee.cfg_max_term_size cfg_twee `max` cfg_max_size } $
    runConditionals constants $
    fmap (reverse . snd) $ flip execStateT (1, []) main
