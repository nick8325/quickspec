{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RecordWildCards, TemplateHaskell, UndecidableInstances, DefaultSignatures, FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
module QuickSpec.Haskell where

import QuickSpec.Haskell.Resolve
import QuickSpec.Type
import QuickSpec.Prop
import QuickSpec.Pruning
import Test.QuickCheck hiding (total)
import Data.Constraint
import Data.Proxy
import qualified Twee.Base as B
import QuickSpec.Term
import Data.Functor.Identity
import Data.Maybe
import Data.MemoUgly
import Test.QuickCheck.Gen.Unsafe
import Data.Char
import Data.Ord
import qualified QuickSpec.Testing.QuickCheck as QuickCheck
import qualified QuickSpec.Pruning.Twee as Twee
import QuickSpec.Explore hiding (quickSpec)
import qualified QuickSpec.Explore
import QuickSpec.Explore.PartialApplication
import QuickSpec.Explore.Polymorphic(Universe(..), universe)
import QuickSpec.Pruning.Background(Background)
import Control.Monad
import Control.Monad.Trans.State.Strict
import QuickSpec.Terminal
import Text.Printf
import Data.Reflection hiding (D)
import QuickSpec.Utils
import GHC.TypeLits
import QuickSpec.Explore.Conditionals
import Control.Spoon
import qualified Data.Set as Set
import qualified Test.QuickCheck.Poly as Poly
import Numeric.Natural
import Test.QuickCheck.Instances()
import Data.List (nub)
import qualified Twee.Term as T

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
    inst (\(obs :: ObserveData A B) -> WrappedObserveData (toValue obs))]

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
-- For an example of using observational equality, see @<https://github.com/nick8325/quickspec/tree/master/examples/PrettyPrinting.hs PrettyPrinting.hs>@.
--
-- You must use `QuickSpec.inst` to add the @Observe@ instance to your signature.
-- Note that `QuickSpec.monoType` requires an `Ord` instance, so this even applies for
-- monomorphic types. Don't forget to add the `Arbitrary` instance too in that case.
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
evalHaskell :: (Given Type, Typed f, PrettyTerm f, Eval f (Value Identity) Maybe) => TestCase -> Term f -> Either (Value Ordy) (Term f)
evalHaskell (TestCase env obs) t =
  maybe (Right t) Left $ do
    Identity val `In` w <- unwrap <$> eval env (defaultTo given t)
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
      (con_name con, twiddle (arity con), typ con)
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

instance Arity Constant where
  arity = typeArity . typ

instance Predicate Constant where
  classify = con_classify

instance (Given Type, Given Instances) => Eval Constant (Value Identity) Maybe where
  eval _ Constant{..} = foldM app con_value con_constraints
    where
      app val constraint = do
        dict <- findValue given constraint
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

-- A `suchThat` generator for a predicate
genSuchThat :: (Predicateable a, Arbitrary (PredicateTestCase a)) => a -> Gen (TestCaseWrapped x (PredicateTestCase a))
genSuchThat p = TestCaseWrapped <$> arbitrary `suchThat` uncrry p

true :: Constant
true = con "True" True

trueTerm :: Term (PartiallyApplied Constant)
trueTerm = App (total true) []

-- | Declare a predicate with a given name and value.
-- The predicate should have type @... -> Bool@.
predicate :: forall a. ( Predicateable a
             , Typeable a
             , Typeable (PredicateTestCase a))
             => String -> a -> (Instances, Constant)
predicate name pred =
  case someSymbolVal name of
    SomeSymbol (_ :: Proxy sym) ->
      let
        instances =
          inst (\(dict :: Dict (Arbitrary (PredicateTestCase a))) -> (withDict dict genSuchThat) pred :: Gen (TestCaseWrapped sym (PredicateTestCase a)))
          `mappend`
          inst (Names [name ++ "_var"] :: Names (TestCaseWrapped sym (PredicateTestCase a)))

        conPred = (con name pred) { con_classify = Predicate conSels ty (App true []) }
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

        ty = typeRep (Proxy :: Proxy (TestCaseWrapped sym (PredicateTestCase a)))
      in
        (instances, conPred)

data Config =
  Config {
    cfg_quickCheck :: QuickCheck.Config,
    cfg_twee :: Twee.Config,
    cfg_max_size :: Int,
    cfg_instances :: Instances,
    cfg_constants :: [[Constant]],
    cfg_predicates :: [[(Instances, Constant)]],
    cfg_default_to :: Type,
    cfg_infer_instance_types :: Bool
    }

makeLensAs ''Config
  [("cfg_quickCheck", "lens_quickCheck"),
   ("cfg_twee", "lens_twee"),
   ("cfg_max_size", "lens_max_size"),
   ("cfg_instances", "lens_instances"),
   ("cfg_constants", "lens_constants"),
   ("cfg_predicates", "lens_predicates"),
   ("cfg_default_to", "lens_default_to"),
   ("cfg_infer_instance_types", "lens_infer_instance_types")]

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_quickCheck = QuickCheck.Config { QuickCheck.cfg_num_tests = 1000, QuickCheck.cfg_max_test_size = 20, QuickCheck.cfg_fixed_seed = Nothing },
    cfg_twee = Twee.Config { Twee.cfg_max_term_size = minBound, Twee.cfg_max_cp_depth = maxBound },
    cfg_max_size = 7,
    cfg_instances = mempty,
    cfg_constants = [],
    cfg_predicates = [],
    cfg_default_to = typeRep (Proxy :: Proxy Int),
    cfg_infer_instance_types = False }

-- Extra types for the universe that come from in-scope instances.
instanceTypes :: Instances -> Config -> [Type]
instanceTypes insts Config{..}
  | not cfg_infer_instance_types = []
  | otherwise =
    snd <$> (concat . concat)
      [ [ tv
        | Just tv <- map (fmap T.substToList . T.unify cls) groundConclusions]
        | cls <- allTCCons ]
  where
    {- Adding types to the universe for type class instantiation -}
    allTypes = map (typ . con_value) (concat cfg_constants)
    allTCCons = gatherTypeClasses allTypes
    groundConclusions = groundInstances gatherInstanceTypes

    -- Gather up all type class constraints in a list of function and constant types 
    gatherTypeClasses :: [Type] -> [Type]
    gatherTypeClasses ts =
      let dicts  = nub . concat $ [ take (dictArity t) (typeArgs t) | t <- ts, dictArity t > 0]
          consts = [ c | Just c <- getDictionary <$> dicts ]
      in consts
    
    gatherInstanceTypes :: [Type]
    gatherInstanceTypes = map (typeRes . valueType . unPoly) . is_instances $ insts
    
    -- Takes a list of [X :- Y] and returns only the Ys where X = ()
    -- and Y is monomorphic
    groundInstances :: [Type] -> [Type]
    groundInstances ts =
      let allConclusions =
                  [ conclusion
                  | [head, conclusion] <- map (T.unpack . T.children) ts
                  , head == (typeRep (Proxy :: Proxy (() :: Constraint)))
                  , not . any T.isVar $ T.subterms conclusion
                  ]
      in allConclusions

data Warnings =
  Warnings {
    warn_no_generator :: [Type],
    warn_no_observer :: [Type] }

warnings :: Instances -> Config -> Warnings
warnings insts cfg@Config{..} =
  Warnings {
    warn_no_generator =
      [ ty | ty <- univ, isNothing (findGenerator cfg_default_to insts ty) ],
    warn_no_observer =
      [ ty | ty <- univ, isNothing (findObserver insts ty) ] }
  where
    -- Check after defaulting types to Int (or whatever it is)
    univ =
      defaultTo cfg_default_to . Set.toList . univ_types $
        universe (instanceTypes insts cfg ++ map typ (concat cfg_constants))

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

quickSpec :: Config -> IO ()
quickSpec cfg@Config{..} = do
  let
    constantsOf f = true:f cfg_constants ++ concatMap selectors (f cfg_constants)
    constants = constantsOf concat
    
    univ = conditionalsUniverse (instanceTypes instances cfg) constants
    instances = cfg_instances `mappend` baseInstances

  give cfg_default_to $ give instances $ do
    let
      present prop = do
        n :: Int <- get
        put (n+1)
        norm <- normaliser
        putLine (printf "%3d. %s" n (show (prettyProp (names instances) (ac norm (conditionalise prop)) <+> maybeType prop)))

      -- Transform x+(y+z) = y+(x+z) into associativity, if + is commutative
      ac norm (lhs :=>: App f [Var x, App f1 [Var y, Var z]] :=: App f2 [Var y1, App f3 [Var x1, Var z1]])
        | f == f1, f1 == f2, f2 == f3,
          x == x1, y == y1, z == z1,
          x /= y, y /= z, x /= z,
          norm (App f [Var x, Var y]) == norm (App f [Var y, Var x]) =
            lhs :=>: App f [App f [Var x, Var y], Var z] :=: App f [Var x, App f [Var y, Var z]]
      ac _ prop = prop

      -- Add a type signature when printing the equation x = y.
      maybeType (_ :=>: x@(Var _) :=: Var _) =
        text "::" <+> pPrintType (typ x)
      maybeType _ = pPrintEmpty

      -- XXX do this during testing
      constraintsOk (Partial f _) = constraintsOk1 f
      constraintsOk (Apply _) = True
      constraintsOk1 = memo $ \con ->
        or [ and [ isJust (findValue instances (defaultTo cfg_default_to constraint)) | constraint <- con_constraints (typeSubst sub con) ]
           | ty <- Set.toList (univ_types univ),
             sub <- maybeToList (matchType (typeRes (typ con)) ty) ]

      enumerator cons =
        sortTerms measure $
        filterEnumerator (all constraintsOk . funs) $
        enumerateConstants atomic `mappend` enumerateApplications
        where
          atomic = cons ++ [Var (V typeVar 0)]

      mainOf f g = do
        putLine $ show $ pPrintSignature
          (map (partial . unhideConstraint) (f cfg_constants))
        putLine ""
        putText (prettyShow (warnings instances cfg))
        putLine "== Laws =="
        QuickSpec.Explore.quickSpec present (flip evalHaskell) cfg_max_size univ
          (enumerator [partial fun | fun <- constantsOf g])
        putLine ""

      main = mapM_ round [1..rounds]
        where
          round n = mainOf (concat . take 1 . drop (rounds-n)) (concat . drop (rounds-n))
          rounds = length cfg_constants

    join $
      fmap withStdioTerminal $
      generate $
      QuickCheck.run cfg_quickCheck (arbitraryTestCase cfg_default_to instances) evalHaskell $
      Twee.run cfg_twee { Twee.cfg_max_term_size = Twee.cfg_max_term_size cfg_twee `max` cfg_max_size } $
      runConditionals (map total constants) $
      flip evalStateT 1 $
        main
