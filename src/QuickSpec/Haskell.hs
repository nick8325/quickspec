{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RecordWildCards, TemplateHaskell #-}
module QuickSpec.Haskell where

import QuickSpec.Haskell.Resolve
import QuickSpec.Type
import QuickSpec.Prop
import Test.QuickCheck hiding (total)
import Data.Constraint
import Data.Proxy
import qualified Twee.Base as B
import QuickSpec.Term
import Data.Functor.Identity
import Data.Maybe
import Data.MemoUgly
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import System.Random
import Data.Char
import Data.Ord
import qualified QuickSpec.Testing.QuickCheck as QuickCheck
import qualified QuickSpec.Pruning.Twee as Twee
import qualified QuickSpec.Explore
import QuickSpec.Explore.PartialApplication
import QuickSpec.Pruning.Background(Background)
import Control.Monad
import Control.Monad.Trans.State.Strict
import QuickSpec.Terminal
import Text.Printf
import Data.Reflection hiding (D)
import QuickSpec.Utils
import GHC.TypeLits
import QuickSpec.Explore.Conditionals

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
    inst (Names ["x", "y", "z", "w"] :: Names A),
    -- Standard instances
    baseType (Proxy :: Proxy ()),
    baseType (Proxy :: Proxy Int),
    baseType (Proxy :: Proxy Integer),
    baseType (Proxy :: Proxy Bool),
    baseType (Proxy :: Proxy Char),
    inst (Sub Dict :: () :- CoArbitrary ()),
    inst (Sub Dict :: () :- CoArbitrary Int),
    inst (Sub Dict :: () :- CoArbitrary Integer),
    inst (Sub Dict :: () :- CoArbitrary Bool),
    inst (Sub Dict :: () :- CoArbitrary Char),
    inst (Sub Dict :: Eq A :- Eq [A]),
    inst (Sub Dict :: Ord A :- Ord [A]),
    inst (Sub Dict :: Arbitrary A :- Arbitrary [A]),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary [A]),
    inst (Sub Dict :: Eq A :- Eq (Maybe A)),
    inst (Sub Dict :: Ord A :- Ord (Maybe A)),
    inst (Sub Dict :: Arbitrary A :- Arbitrary (Maybe A)),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary (Maybe A)),
    inst (Sub Dict :: (Eq A, Eq B) :- Eq (A, B)),
    inst (Sub Dict :: (Ord A, Ord B) :- Ord (A, B)),
    inst (Sub Dict :: (Arbitrary A, Arbitrary B) :- Arbitrary (A, B)),
    inst (Sub Dict :: (CoArbitrary A, CoArbitrary B) :- CoArbitrary (A, B)),
    inst (Sub Dict :: (CoArbitrary A, Arbitrary B) :- Arbitrary (A -> B)),
    inst (Sub Dict :: (Arbitrary A, CoArbitrary B) :- CoArbitrary (A -> B)),
    inst (Sub Dict :: Ord A :- Eq A),
    -- From Arbitrary to Gen
    inst $ \(Dict :: Dict (Arbitrary A)) -> arbitrary :: Gen A,
    inst $ \(dict :: Dict ClassA) -> return dict :: Gen (Dict ClassA),
    -- From Dict to OrdDict
    inst (OrdDict :: Dict (Ord A) -> OrdDict A),
    -- Observe
    inst (\(Dict :: Dict (Ord A)) -> Observe (return id) :: Observe A A),
    inst (\(Observe obsm :: Observe B C) (xm :: Gen A) ->
      Observe (do {x <- xm; obs <- obsm; return (\f -> obs (f x))}) :: Observe (A -> B) C),
    inst (\(obs :: Observe A B) -> Observe1 (toValue obs))]

data Observe a b where
  Observe :: Ord b => Gen (a -> b) -> Observe a b
  deriving Typeable
data Observe1 a = Observe1 (Value (Observe a)) deriving Typeable

observe :: Ord res => Gen env -> (env -> val -> res) -> Observe val res
observe gen f =
  Observe (do { env <- gen; return (\x -> f env x) })
  

-- data SomeObserve a = forall args res. (Ord res, Arbitrary args) => SomeObserve (a -> args -> res) deriving Typeable

newtype OrdDict a = OrdDict (Dict (Ord a)) deriving Typeable

baseType :: forall proxy a. (Ord a, Arbitrary a, Typeable a) => proxy a -> Instances
baseType _ =
  mconcat [
    inst (Dict :: Dict (Ord a)),
    inst (Dict :: Dict (Arbitrary a))]

newtype Names a = Names { getNames :: [String] }

names :: Instances -> Type -> [String]
names insts ty =
  case findInstance insts (skolemiseTypeVars ty) of
    (x:_) -> ofValue getNames x
    [] -> error "don't know how to name variables"

arbitraryVal :: Type -> Instances -> Gen (Var -> Value Maybe, Value Identity -> Maybe (Value Ordy))
arbitraryVal def insts =
  MkGen $ \g n ->
    let (g1, g2) = split g in
    (memo $ \(V ty x) ->
       case genType ty of
         Nothing ->
           fromJust $ cast (defaultTo def ty) (toValue (Nothing :: Maybe A))
         Just gen ->
           forValue gen $ \gen ->
             Just (unGen (coarbitrary x gen) g1 n),
     ordyVal g2 n)
  where
    genType :: Type -> Maybe (Value Gen)
    genType = memo $ \ty ->
      case findInstance insts (defaultTo def ty) of
        [] -> Nothing
        (gen:_) ->
          Just (mapValue (coarbitrary ty) gen)

    ordyVal :: QCGen -> Int -> Value Identity -> Maybe (Value Ordy)
    ordyVal g n x =
      let ty = defaultTo def (typ x) in
      case ordyTy ty of
        Nothing -> Nothing
        Just f -> Just (unGen f g n x)

    ordyTy :: Type -> Maybe (Gen (Value Identity -> Value Ordy))
    ordyTy = memo $ \ty ->
      case findInstance insts ty :: [Value Observe1] of
        [] -> Nothing
        (val:_) ->
          case unwrap val of
            Observe1 val `In` w1 ->
              case unwrap val of
                Observe obs `In` w2 ->
                  Just $
                    MkGen $ \g n ->
                      let observe = unGen obs g n in
                      \x -> wrap w2 (Ordy (observe (runIdentity (reunwrap w1 x))))

data Ordy a where Ordy :: Ord a => a -> Ordy a
instance Eq (Value Ordy) where x == y = compare x y == EQ

instance Ord (Value Ordy) where
  compare x y =
    compare (typ x) (typ y) `mappend`
    case unwrap x of
      Ordy xv `In` w ->
        let Ordy yv = reunwrap w y in
        compare xv yv

evalHaskell :: (Given Type, Typed f, PrettyTerm f, Eval f (Value Maybe)) => (Var -> Value Maybe, Value Identity -> Maybe (Value Ordy)) -> Term f -> Either (Value Ordy) (Term f)
evalHaskell (env, obs) t =
  case unwrap (eval env t) of
    Nothing `In` _ -> Right t
    Just val `In` w ->
      case obs (wrap w (Identity val)) of
        Nothing -> Right t
        Just ordy -> Left ordy

data Constant =
  Constant {
    con_name  :: String,
    con_style :: TermStyle,
    con_pretty_arity :: Int,
    con_value :: Value Identity,
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
    con_size = 1,
    con_classify = Function }

isOp :: String -> Bool
isOp "[]" = False
isOp ('"':_) = False
isOp xs | all (== '.') xs = True
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_' || x == '.'

instance Typed Constant where
  typ = typ . con_value
  typeSubst_ sub con =
    con { con_value = typeSubst_ sub (con_value con),
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

instance (Given Type, Applicative f) => Eval Constant (Value f) where
  eval _ = mapValue (pure . runIdentity) . con_value

class Predicateable a where
  uncrry :: a -> TestCase a -> Bool

instance Predicateable Bool where
  uncrry = const

instance forall a b. (Predicateable b, Typeable a, TestCase (a -> b) ~ (a, TestCase b)) => Predicateable (a -> b) where
  uncrry f (a, b) = uncrry (f a) b

-- Foldr over functions
type family (Foldr f b fun) :: * where
  Foldr f def (a -> b) = f a (Foldr f def b)
  Foldr f def b        = def

-- A test case for predicates of type a
-- if `a ~ A -> B -> C -> Bool` we get `TestCase a ~ (A, (B, (C, ())))`
--
-- Some speedup should be possible by using unboxed tuples instead...
type TestCase a = Foldr (,) () a

data TestCaseWrapped (t :: Symbol) a = TestCaseWrapped { unTestCaseWrapped :: a }

-- A `suchThat` generator for a predicate
genSuchThat :: (Predicateable a, Arbitrary (TestCase a)) => a -> Gen (TestCaseWrapped x (TestCase a))
genSuchThat p = TestCaseWrapped <$> arbitrary `suchThat` uncrry p

data PredRep = PredRep { predInstances :: Instances
                       , predCon :: Constant
                       , predCons :: [Constant] }

true :: Constant
true = con "True" True

trueTerm :: Term (PartiallyApplied Constant)
trueTerm = App (total true) []

-- | Declare a predicate with a given name and value.
-- The predicate should have type @... -> Bool@.
predicate :: forall a. ( Predicateable a
             , Typeable a
             , Typeable (TestCase a))
             => String -> a -> PredRep
predicate name pred =
  case someSymbolVal name of
    SomeSymbol (_ :: Proxy sym) ->
      let
        instances =
          inst (\(dict :: Dict (Arbitrary (TestCase a))) -> (withDict dict genSuchThat) pred :: Gen (TestCaseWrapped sym (TestCase a)))
          `mappend`
          inst (Names [name ++ "_var"] :: Names (TestCaseWrapped sym (TestCase a)))

        conPred = (con name pred) { con_classify = Predicate conSels ty (App true []) }
        conSels = [ (constant' (name ++ "_" ++ show i) (select i)) { con_classify = Selector i conPred ty, con_size = 0 } | i <- [0..typeArity (typeOf pred)-1] ]

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

        ty = typeRep (Proxy :: Proxy (TestCaseWrapped sym (TestCase a)))
      in
        PredRep instances conPred (conPred:conSels)

data Config =
  Config {
    cfg_quickCheck :: QuickCheck.Config,
    cfg_twee :: Twee.Config,
    cfg_max_size :: Int,
    cfg_instances :: Instances,
    cfg_constants :: [[Constant]],
    cfg_predicates :: [[PredRep]],
    cfg_default_to :: Type }

makeLensAs ''Config
  [("cfg_quickCheck", "lens_quickCheck"),
   ("cfg_twee", "lens_twee"),
   ("cfg_max_size", "lens_max_size"),
   ("cfg_instances", "lens_instances"),
   ("cfg_constants", "lens_constants"),
   ("cfg_predicates", "lens_predicates"),
   ("cfg_default_to", "lens_default_to")]

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_quickCheck = QuickCheck.Config { QuickCheck.cfg_num_tests = 1000, QuickCheck.cfg_max_test_size = 20 },
    cfg_twee = Twee.Config { Twee.cfg_max_term_size = minBound, Twee.cfg_max_cp_depth = maxBound },
    cfg_max_size = 7,
    cfg_instances = mempty,
    cfg_constants = [],
    cfg_predicates = [],
    cfg_default_to = typeRep (Proxy :: Proxy Int) }

quickSpec :: Config -> IO ()
quickSpec Config{..} = give cfg_default_to $ do
  let
    constantsOf f = true:f cfg_constants ++ f (map (concatMap predCons) cfg_predicates)
    constants = constantsOf concat
    univ = conditionalsUniverse constants
    instances = mconcat (cfg_instances:map predInstances (concat cfg_predicates) ++ [baseInstances])

    present prop = do
      n :: Int <- get
      put (n+1)
      putLine (printf "%3d. %s" n (show (prettyProp (names instances) (conditionalise prop))))

    mainOf f g = do
      printConstants (f cfg_constants ++ f (map (map predCon) cfg_predicates))
      putLine ""
      putLine "== Laws =="
      QuickSpec.Explore.quickSpec present measure (flip evalHaskell) cfg_max_size univ
        [ Partial fun 0 | fun <- constantsOf g ]
      putLine ""

    main = mapM_ round [0..rounds-1]
      where
        round n = mainOf (concat . drop n . take (n+1) . reverse) (concat . take (n+1) . reverse)
        rounds = max (length cfg_constants) (length cfg_predicates)

  join $
    fmap withStdioTerminal $
    generate $
    QuickCheck.run cfg_quickCheck (arbitraryVal cfg_default_to instances) evalHaskell $
    Twee.run cfg_twee { Twee.cfg_max_term_size = Twee.cfg_max_term_size cfg_twee `max` cfg_max_size } $
    runConditionals (map total constants) $
    flip evalStateT 1 $
      main

printConstants :: MonadTerminal m => [Constant] -> m ()
printConstants cs = do
  putLine "== Functions =="
  let
    decls = [ (show (pPrint (App (Partial c 0) [])), pPrintType (typ c)) | c <- cs ]
    maxWidth = maximum (0:map (length . fst) decls)
    pad xs = replicate (maxWidth - length xs) ' ' ++ xs
    pPrintDecl (name, ty) =
      hang (text (pad name) <+> text "::") 2 ty

  mapM_ (putLine . show . pPrintDecl) decls
