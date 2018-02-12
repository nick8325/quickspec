{-# LANGUAGE ScopedTypeVariables, TypeOperators, GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RecordWildCards #-}
module QuickSpec.Haskell where

import QuickSpec.Haskell.Resolve
import QuickSpec.Type
import QuickSpec.Prop
import Test.QuickCheck
import Data.Constraint
import Data.Proxy
import qualified Twee.Base as B
import QuickSpec.Term
import Data.Functor.Identity
import Data.Maybe
import Data.MemoUgly
import Test.QuickCheck.Gen
import System.Random
import Data.Char
import Data.Ord
import qualified QuickSpec.Testing.QuickCheck as QuickCheck
import qualified QuickSpec.Pruning.Twee as Twee
import qualified QuickSpec.Explore
import QuickSpec.Explore.PartialApplication
import QuickSpec.Pruning.Background(Background)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import QuickSpec.Terminal
import QuickSpec.Explore.Polymorphic
import Text.Printf
import Debug.Trace
import Data.Reflection hiding (D)

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
    inst (Names ["x", "y", "z"] :: Names A),
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
    inst (Sub Dict :: (CoArbitrary A, Arbitrary B) :- Arbitrary (A -> B)),
    inst (Sub Dict :: Eq A :- Eq [A]),
    inst (Sub Dict :: Ord A :- Ord [A]),
    inst (Sub Dict :: Arbitrary A :- Arbitrary [A]),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary [A]),
    inst (Sub Dict :: Eq A :- Eq (Maybe A)),
    inst (Sub Dict :: Ord A :- Ord (Maybe A)),
    inst (Sub Dict :: Arbitrary A :- Arbitrary (Maybe A)),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary (Maybe A)),
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

defaultTo :: Typed a => Type -> a -> a
defaultTo def = typeSubst (const def)

arbitraryVal :: Type -> Instances -> Gen (Var -> Value Maybe, Value Identity -> Maybe TestResult)
arbitraryVal def insts =
  MkGen $ \g n ->
    let (g1, g2) = split g in
    (memo $ \(V ty x) ->
       case typ ty of
         Nothing ->
           fromJust $ cast ty (toValue (Nothing :: Maybe A))
         Just gen ->
           forValue gen $ \gen ->
             Just (unGen (coarbitrary x gen) g1 n),
     unGen (ordyVal def insts) g2 n) 
  where
    typ :: Type -> Maybe (Value Gen)
    typ = memo $ \ty ->
      case findInstance insts (defaultTo def ty) of
        [] -> Nothing
        (gen:_) ->
          Just (mapValue (coarbitrary ty) gen)

ordyVal :: Type -> Instances -> Gen (Value Identity -> Maybe TestResult)
ordyVal def insts =
  MkGen $ \g n -> \x ->
    case ordyTy (typ x) of
      Nothing -> Nothing
      Just f -> Just (TestResult (typ x) (unGen f g n x))
  where
    ordyTy :: Type -> Maybe (Gen (Value Identity -> Value Ordy))
    ordyTy = memo $ \ty ->
      case findInstance insts (defaultTo def ty) :: [Value Observe1] of
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

data TestResult = TestResult Type (Value Ordy) deriving (Eq, Ord, Show)

data Ordy a where Ordy :: Ord a => a -> Ordy a
instance Eq (Value Ordy) where x == y = compare x y == EQ

instance Ord (Value Ordy) where
  compare x y =
    compare (typ x) (typ y) `mappend`
    case unwrap x of
      Ordy xv `In` w ->
        let Ordy yv = reunwrap w y in
        compare xv yv

evalHaskell :: (Typed f, PrettyTerm f, Eval f (Value Maybe)) => (Var -> Value Maybe, Value Identity -> Maybe TestResult) -> Term f -> Either TestResult (Term f)
evalHaskell (env, obs) t =
  case unwrap (eval env t) of
    Nothing `In` _ -> trace ("couldn't evaluate " ++ prettyShow t ++ " :: " ++ prettyShow (typ t)) $ Right t
    Just val `In` w ->
      case obs (wrap w (Identity val)) of
        Nothing -> trace ("no observer for " ++ prettyShow t) $ Right t
        Just ordy -> Left ordy

data Constant =
  Constant {
    con_name  :: String,
    con_style :: TermStyle,
    con_pretty_arity :: Int,
    con_value :: Value Identity }

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

constant :: Typeable a => String -> a -> Constant
constant name val =
  Constant {
    con_name = name,
    con_style =
      case () of
        _ | name == "()" -> curried
          | take 1 name == "," -> fixedArity (length name+1) tupleStyle
          | take 2 name == "(," -> fixedArity (length name-1) tupleStyle
          | isOp name && typeArity (typeOf val) >= 2 -> infixStyle 5
          | isOp name -> prefix
          | otherwise -> curried,
    con_pretty_arity =
      case () of
        _ | isOp name && typeArity (typeOf val) >= 2 -> 2
          | isOp name -> 1
          | otherwise -> 0,
    con_value = toValue (Identity val) }

isOp :: String -> Bool
isOp "[]" = False
isOp ('"':_) = False
isOp xs | all (== '.') xs = True
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_' || x == '.'

instance Typed Constant where
  typ = typ . con_value
  typeSubst_ sub con = con { con_value = typeSubst_ sub (con_value con) }

instance Pretty Constant where
  pPrint = text . con_name

instance PrettyTerm Constant where
  termStyle = con_style

instance PrettyArity Constant where
  prettyArity = con_pretty_arity

instance Sized Constant where
  size _ = 1

instance Arity Constant where
  arity = typeArity . typ

instance (Given Type, Applicative f) => Eval Constant (Value f) where
  eval _ = mapValue (pure . runIdentity) . defaultTo given . con_value

data Config =
  Config {
    cfg_quickCheck :: QuickCheck.Config,
    cfg_twee :: Twee.Config,
    cfg_max_size :: Int,
    cfg_instances :: Instances }

defaultConfig :: Config
defaultConfig =
  Config {
    cfg_quickCheck = QuickCheck.Config { QuickCheck.cfg_num_tests = 1000, QuickCheck.cfg_max_test_size = 20 },
    cfg_twee = Twee.Config { Twee.cfg_max_term_size = minBound, Twee.cfg_max_cp_depth = 2 },
    cfg_max_size = 7,
    cfg_instances = mempty }

quickSpec :: Config -> [Constant] -> Type -> [Type] -> IO ()
quickSpec Config{..} funs ty tys = give ty $ do
  let
    instances = cfg_instances `mappend` baseInstances
    present prop = do
      n :: Int <- get
      put (n+1)
      putLine (printf "%3d. %s" n (show (prettyProp (names instances) prop)))
  join $
    fmap withStdioTerminal $
    generate $
    QuickCheck.run cfg_quickCheck (arbitraryVal ty instances) evalHaskell $
    Twee.run cfg_twee { Twee.cfg_max_term_size = Twee.cfg_max_term_size cfg_twee `max` cfg_max_size } $
    flip evalStateT 1 $
    QuickSpec.Explore.quickSpec present measure (flip evalHaskell) cfg_max_size
      [Partial f 0 | f <- funs]
      ty
      tys
