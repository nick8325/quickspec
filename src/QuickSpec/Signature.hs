-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, Rank2Types, StandaloneDeriving, TypeOperators, FlexibleContexts, KindSignatures, GeneralizedNewtypeDeriving, GADTs, PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module QuickSpec.Signature where

#include "errors.h"
import Control.Applicative
import Control.Monad hiding (sequence)
import Control.Monad.Trans.State.Strict
import Data.Char hiding (ord)
import Data.Constraint
import Data.Functor.Identity
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Traversable hiding (mapM)
import Prelude hiding (sequence)
import QuickSpec.Prop hiding (Predicate)
import QuickSpec.Parse
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.PredicatesInterface
import System.Timeout
import Test.QuickCheck hiding (subterms, Fun)
import Data.Ord
import {-# SOURCE #-} QuickSpec.Pruning.Completion(Completion)
import {-# SOURCE #-} QuickSpec.Pruning.Simple(SimplePruner)
import Twee.Base
import qualified Twee.Label as Label
import QuickSpec.Utils
import Data.Proxy
import qualified Data.Typeable as Typeable
import QuickSpec.Resolve
import QuickSpec.NamesFor

deriving instance Typeable Ord
deriving instance Typeable Arbitrary
deriving instance Typeable CoArbitrary
deriving instance Typeable Gen

type PrunerType = Completion

-- | The entire QuickSpec configuration.
-- The only fields you will probably need are
-- `constants`, `instances`, `predicates` and `maxTermSize`.
--
-- As a simple example, the following signature explores @++@ and @reverse@:
--
-- @
-- sig =
--   `signature` {
--      `constants` = [
--        `constant` "reverse" (reverse :: [`A`] -> [`A`]),
--        `constant` "++" ((++) :: [`A`] -> [`A`] -> [`A`]) ]}
-- @
--
-- To test a user-defined datatype, use `baseType`:
--
-- @
-- data T = ...
-- sig =
--   `signature` {
--     `constants` = ...,
--     `instances` = [`baseType` (undefined :: T)] }
-- @
--
-- To test a /polymorphic/ user-defined datatype, you will need to use `inst` or
-- `makeInstance` to declare `Ord` and `Arbitrary` instances:
--
-- @
-- data T a = ...
-- sig =
--   `signature` {
--      `constants` = ...,
--      `instances` = [
--        `inst` (`Sub` `Dict` :: Ord `A` `:-` Ord (T `A`)),
--        `inst` (`Sub` `Dict` :: Arbitrary `A` `:-` Arbitrary (T `A`)) ]}
-- @
--
-- or:
--
-- @
-- data T a = ...
-- sig =
--   `signature` {
--      `constants` = ...,
--      `instances` = [
--        `makeInstance` (\(Dict :: Dict (Ord A) -> Dict :: Dict (Ord (T A)))),
--        `makeInstance` (\(Dict :: Dict (Arbitrary A) -> Dict :: Dict (Arbitrary (T A)))) ]}
-- @
--
-- Instead of an `Arbitrary` and `Ord` instance, it is possible to supply a
-- generator and an observational equality function; see @examples/PrettyPrinting.hs@.
data Signature =
  Signature {
    -- | The constants and functions to explore. Created by using `constant`.
    constants           :: [Constant],
    -- | Typeclass instances for testing. Created by using `baseType`, `inst` or `makeInstance`.
    instances           :: Instances,
    -- | Predicates for use in conditional equations. Created by using `predicate`.
    predicates          :: [Predicate],
    -- | A type which type variables default to for testing.
    defaultTo           :: Maybe Typeable.TypeRep,
    -- | The maximum size of terms to explore (default: 7).
    maxTermSize         :: Maybe Int,
    -- | The maximum depth of terms to explore (default: unlimited).
    maxTermDepth        :: Maybe Int,
    -- | The number of test cases to try for each law (default: 1000).
    maxTests            :: Maybe Int,
    -- | For experts: a list of properties which are already known to be true.
    background          :: [Prop],
    -- | For experts: a timeout for running test cases.
    testTimeout         :: Maybe Int,
    -- | For experts: the maximum size of terms to reason about during pruning.
    maxPruningSize      :: Maybe Int,
    -- | For experts: below this size all schemas are instantiated.
    maxCommutativeSize  :: Maybe Int,
    -- | For experts: a function which is called to simplify discovered laws.
    simplify            :: Maybe (Signature -> Prop -> Prop),
    -- | For experts: an extra function used to prune the discovered laws.
    extraPruner         :: Maybe ExtraPruner,
    -- | For experts: print internal statistics.
    printStatistics     :: Bool,
    -- | For experts: don't print anything out.
    silent              :: Bool,
    -- | Internal use: the initial state of the pruner.
    theory              :: Maybe PrunerType,
    -- | Internal use: for conditionals.
    conditionalsContext :: [(Constant, [Constant])],
    -- | Internal use: for conditionals.
    predicatesI         :: [PredRep]
  }
  deriving Typeable

instance Pretty Signature where
  pPrint sig = vcat (map prettyDecl decls)
    where
      decls = [(show (pPrint (app c [])), pPrintType (canonicalise (typ c))) | c <- constants sig, not (conIsBackground c), not (conIsHidden c) ]
      maxWidth = maximum (0:map (length . fst) decls)
      pad xs = replicate (maxWidth - length xs) ' ' ++ xs
      prettyDecl (name, ty) =
        hang (text (pad name) <+> text "::") 2 ty

      as = supply [[x] | x <- ['a'..'z']]
      prettyType ty = build (aux (singleton ty))
      aux Empty = mempty
      aux (Cons (Var (MkVar x)) ts) =
        con (toFun (L (Name (as !! x)))) `mappend` aux ts
      aux (Cons (Fun f ts) us) =
        fun (toFun (R (fromFun f))) (aux ts) `mappend` aux us

      pPrintType ty =
        case cs of
          []  -> pPrint (prettyType ty')
          [c] -> pPrint (prettyType c) <+> text "=>" <+> pPrint (prettyType ty')
          _   -> parens (hsep (punctuate comma (map (pPrint . prettyType) cs))) <+> pPrint (prettyType ty')
        where
          (cs, ty') = loop [] ty
          loop cs (App Arrow [arg, res])
            | Just c <- getDictionary arg =
              loop (cs ++ [c]) res
          loop cs ty = (cs, ty)

defaultTypes :: Typed a => Signature -> a -> a
defaultTypes sig = typeSubst (const (defaultTo_ sig))

defaultTo_ :: Signature -> Type
defaultTo_ sig =
  case defaultTo sig of
    Nothing -> typeOf (undefined :: Int)
    Just ty -> fromTypeRep ty

maxTermSize_ :: Signature -> Int
maxTermSize_ = fromMaybe 7 . maxTermSize

maxPruningSize_ :: Signature -> Int
maxPruningSize_ sig =
  max (fromMaybe 0 (maxPruningSize sig)) (maxTermSize_ sig)

maxCommutativeSize_ sig
  | null (predicatesI sig) = fromMaybe 5 (maxCommutativeSize sig)
  | otherwise = maxTermSize_ sig

maxTests_ :: Signature -> Int
maxTests_ = fromMaybe 1000 . maxTests

testTimeout_ :: Signature -> IO a -> IO (Maybe a)
testTimeout_ sig =
  case testTimeout sig of
    Nothing -> fmap Just
    Just time -> timeout time

simplify_ :: Signature -> Prop -> Prop
simplify_ sig =
  case simplify sig of
    Nothing -> id
    Just f -> f sig

data ExtraPruner = E Int | SPASS Int | Z3 Int | Waldmeister Int | None deriving Show

extraPruner_ :: Signature -> ExtraPruner
extraPruner_ = fromMaybe None . extraPruner

defaultInstances :: Instances
defaultInstances =
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
    inst $ \(NamesFor names :: NamesFor A) ->
      NamesFor (map (++ "s") names) :: NamesFor [A],
    inst (NamesFor ["p", "q", "r"] :: NamesFor (A -> Bool)),
    inst (NamesFor ["f", "g", "h"] :: NamesFor (A -> B)),
    inst (NamesFor ["x", "y", "z"] :: NamesFor A),
    -- Standard instances
    baseType (undefined :: ()),
    baseType (undefined :: Int),
    baseType (undefined :: Integer),
    baseType (undefined :: Bool),
    baseType (undefined :: Char),
    inst (Sub Dict :: () :- CoArbitrary ()),
    inst (Sub Dict :: () :- CoArbitrary Int),
    inst (Sub Dict :: () :- CoArbitrary Integer),
    inst (Sub Dict :: () :- CoArbitrary Bool),
    inst (Sub Dict :: () :- CoArbitrary Char),
    inst (Sub Dict :: Ord A :- Ord [A]),
    inst (Sub Dict :: Arbitrary A :- Arbitrary [A]),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary [A]),
    inst (Sub Dict :: Ord A :- Ord (Maybe A)),
    inst (Sub Dict :: Arbitrary A :- Arbitrary (Maybe A)),
    inst (Sub Dict :: CoArbitrary A :- CoArbitrary (Maybe A)),
    inst (Sub Dict :: Ord A :- Eq A),
    inst (Sub Dict :: (CoArbitrary A, Arbitrary B) :- Arbitrary (A -> B)),
    inst (Sub Dict :: (Arbitrary A, CoArbitrary B) :- CoArbitrary (A -> B)),
    inst (Sub Dict :: (Ord A, Ord B) :- Ord (A, B)),
    inst (Sub Dict :: (Arbitrary A, Arbitrary B) :- Arbitrary (A, B)),
    inst (Sub Dict :: (CoArbitrary A, CoArbitrary B) :- CoArbitrary (A, B)),
    inst (\(dict :: Dict ClassA) -> return dict :: Gen (Dict ClassA)),
    -- From Arbitrary to Gen
    inst $ \(Dict :: Dict (Arbitrary A)) -> arbitrary :: Gen A,
    inst $ \(dict :: Dict ClassA) -> return dict :: Gen (Dict ClassA),
    -- Observe
    inst (\(dict :: Dict (Ord A)) -> Observe dict return),
    inst (\(obs :: Observe A B) -> observeTraversable ins obs :: Observe [A] [B]),
    inst (\(Dict :: Dict (Arbitrary A),
           obs :: Observe B C) -> observeFunction obs :: Observe (A -> B) C ),
    inst (\(obs :: Observe A B) -> Observe1 (toValue obs))]

addDefaultInstances :: Signature -> Signature
addDefaultInstances sig =
  sig { instances = instances sig `mappend` defaultInstances }

data Observe a b = Observe (Dict (Ord b)) (a -> Gen b) deriving Typeable
newtype Observe1 a = Observe1 (Value (Observe a)) deriving Typeable

-- | Declare that values of a particular type should be compared by observational equality.
--
-- See @examples/PrettyPrinting.hs@ for an example.
observe :: Ord b => (a -> Gen b) -> Observe a b
observe = Observe Dict

observeTraversable :: Traversable f => (forall a. Ord a :- Ord (f a)) -> Observe a b -> Observe (f a) (f b)
observeTraversable ins (Observe dict f) =
  Observe (applyInstance dict ins) $ \x -> sequence (fmap f x)
  where
    applyInstance :: Dict c -> (c :- d) -> Dict d
    applyInstance Dict (Sub Dict) = Dict

observeFunction :: Arbitrary a => Observe b c -> Observe (a -> b) c
observeFunction (Observe dict f) =
  Observe dict $ \g -> do { x <- arbitrary; f (g x) }

namesFor_ :: Signature -> Type -> [String]
namesFor_ sig ty =
  case findInstance (instances sig) (skolemiseTypeVars ty) of
    (x:_) -> ofValue unNamesFor x

-- | Declare a new monomorphic type.
baseType :: forall a. (Ord a, Arbitrary a, Typeable a) => a -> Instances
baseType _ =
  mconcat [
    inst (Sub Dict :: () :- Ord a),
    inst (Sub Dict :: () :- Arbitrary a)]

-- | Declare a new monomorphic type, saying how you want variables of that type to be named.
baseTypeNames :: forall a. (Ord a, Arbitrary a, Typeable a) => [String] -> a -> Instances
baseTypeNames xs _ =
  mconcat [
    inst (Sub Dict :: () :- Ord a),
    inst (Sub Dict :: () :- Arbitrary a),
    names (NamesFor xs :: NamesFor a)]

-- | Declare what variable names you would like to use for values of a particular type. See also `baseTypeNames`.
names  :: Typeable a => NamesFor a -> Instances
names x = inst x

names1 :: (Typeable a, Typeable b) => (a -> NamesFor b) -> Instances
names1 x = inst x

instance Monoid Signature where
  mempty =
    Signature {
      constants = [],
      instances = mempty,
      defaultTo = Nothing,
      maxTermSize = Nothing,
      maxTermDepth = Nothing,
      maxTests = Nothing,
      background = [],
      testTimeout = Nothing,
      maxPruningSize = Nothing,
      maxCommutativeSize = Nothing,
      theory = Nothing,
      simplify = Nothing,
      extraPruner = Nothing,
      conditionalsContext = [],
      predicates = [],
      predicatesI = [],
      printStatistics = False,
      silent = False }

  mappend sig1 sig2 =
    Signature {
      constants = constants sig1 ++ constants sig2,
      instances = instances sig1 `mappend` instances sig2,
      defaultTo = defaultTo sig1 `mplus` defaultTo sig2,
      maxTermSize = maxTermSize sig1 `mplus` maxTermSize sig2,
      maxTermDepth = maxTermDepth sig1 `mplus` maxTermDepth sig2,
      maxTests = maxTests sig1 `mplus` maxTests sig2,
      background = background sig1 ++ background sig2,
      testTimeout = testTimeout sig1 `mplus` testTimeout sig2,
      maxPruningSize = maxPruningSize sig1 `mplus` maxPruningSize sig2,
      maxCommutativeSize = maxCommutativeSize sig1 `mplus` maxCommutativeSize sig2,
      theory = theory sig1 `mplus` theory sig2,
      simplify = simplify sig1 `mplus` simplify sig2,
      extraPruner = extraPruner sig1 `mplus` extraPruner sig2,
      conditionalsContext = conditionalsContext sig1 ++ conditionalsContext sig2,
      predicates = predicates sig1 ++ predicates sig2,
      predicatesI = predicatesI sig1 ++ predicatesI sig2,
      printStatistics = printStatistics sig1 || printStatistics sig2,
      silent = silent sig1 || silent sig2 }

-- | An empty signature.
signature :: Signature
signature = mempty

typeUniverse :: Signature -> Set Type
typeUniverse sig =
  Set.fromList $
    build (var (MkVar 0)):
    concatMap collapse
      [ oneTypeVar (typ t) | c@Constant{} <- usort (constants sig ++ map fromFun (funs (background sig))), t <- types (typ c) ]
  where
    types t = typeRes t:typeArgs t ++ concatMap types (typeArgs t)
    collapse ty@(App f tys) =
      build (var (MkVar 0)):ty:
      map (app f) (mapM collapse tys)
    collapse x@Var{} = [x]

data TypeKind = Useless | Partial | Useful deriving (Eq, Show)

typeKind :: Signature -> Type -> TypeKind
typeKind sig ty
  | isDictionary ty = Useful
  | occurs ty = Useful
  | any occurs (suffixes ty) = Partial
  | otherwise = Useless
  where
    suffixes t@(App Arrow [_, u]) = t:suffixes u
    suffixes t = [t]
    occurs t = or [ isJust (match t u) | u <- Set.toList u ]
    u = typeUniverse sig

newtype Name = Name String deriving (Eq, Ord)
instance Pretty Name where
  pPrint (Name x) = text x
instance PrettyTerm Name

instance Numbered Name where
  fromInt = fromMaybe __ . Label.find
  toInt = Label.label
instance Label.Labelled Name where
  cache = nameCache
{-# NOINLINE nameCache #-}
nameCache :: Label.Cache Name
nameCache = Label.mkCache

data Union a b = L a | R b
instance (Pretty a, Pretty b) => Pretty (Union a b) where
  pPrintPrec l p (L x) = pPrintPrec l p x
  pPrintPrec l p (R x) = pPrintPrec l p x
instance (PrettyTerm a, PrettyTerm b) => PrettyTerm (Union a b) where
  termStyle (L x) = termStyle x
  termStyle (R x) = termStyle x
instance (Numbered a, Numbered b) => Numbered (Union a b) where
  fromInt n
    | even n = L (fromInt (n `div` 2))
    | otherwise = R (fromInt (n `div` 2))
  toInt (L x) = 2*toInt x
  toInt (R x) = 2*toInt x+1

prettyRename :: Signature -> Prop -> PropOf (Term (Union Name Constant))
prettyRename sig p = fmap (build . aux . singleton) p
  where
    vs = nub (terms p >>= fromTermList >>= typedVars)
    m = Map.fromList sub
    sub = evalState (mapM assign vs) Set.empty
    assign (ty, v) = do
      s <- get
      let names = supply (namesFor_ sig ty)
          name = head (filter (`Set.notMember` s) names)
      modify (Set.insert name)
      return ((ty, v), Name name)
    aux Empty = mempty
    aux (Cons (App (Id ty) [Var x]) ts) =
      con (toFun (L (Map.findWithDefault __ (ty, x) m))) `mappend` aux ts
    aux (Cons (Fun f ts) us) =
      fun (toFun (R (fromFun f))) (aux ts) `mappend` aux us

addBackground :: [String] -> Signature -> Signature
addBackground props sig =
  sig { background = background sig ++ map (parseProp (constants sig)) props }

printTheory :: Signature -> IO ()
printTheory sig = putStrLn (showTheory (background sig))

predicateSig :: Signature -> Signature
predicateSig sig = let ps             = fixPreds () $ predicates sig in
                       sig {constants = nub $ constants sig ++ (concatMap selectors ps) ++ map predCons ps ++ [constant "True" True | not (null ps)],
                            instances = instances sig `mappend` mconcat (map predInstances ps),
                            conditionalsContext = [(predCons p, selectors p) | p <- ps],
                            predicatesI = ps
                           }

fixPreds :: forall t. Typeable t => t -> [Predicate] -> [PredRep]
fixPreds _ [] = []
fixPreds t (PRW f : ps) = f t : fixPreds ((), t) ps
