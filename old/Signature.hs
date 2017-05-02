-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, Rank2Types, StandaloneDeriving, TypeOperators, FlexibleContexts, KindSignatures, GeneralizedNewtypeDeriving, GADTs #-}
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
import QuickSpec.Instance
import QuickSpec.Prop
import QuickSpec.Parse
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.PredicatesInterface
import System.Timeout
import Test.QuickCheck hiding (subterms)
import Data.Ord
import {-# SOURCE #-} QuickSpec.Pruning.Completion(Completion)
import {-# SOURCE #-} QuickSpec.Pruning.Simple(SimplePruner)
import Twee.Base
import qualified Twee.Label as Label
import QuickSpec.Utils

deriving instance Typeable Ord
deriving instance Typeable Arbitrary
deriving instance Typeable CoArbitrary
deriving instance Typeable Gen

type PrunerType = Completion

data Signature =
  Signature {
    constants           :: [Constant],
    instances           :: Instances,
    background          :: [Prop],
    theory              :: Maybe PrunerType,
    defaultTo           :: Maybe Type,
    maxTermSize         :: Maybe Int,
    maxPruningSize      :: Maybe Int,
    maxTermDepth        :: Maybe Int,
    maxCommutativeSize  :: Maybe Int,
    maxTests            :: Maybe Int,
    testTimeout         :: Maybe Int,
    printStatistics     :: Bool,
    simplify            :: Maybe (Signature -> Prop -> Prop),
    extraPruner         :: Maybe ExtraPruner,
    conditionalsContext :: [(Constant, [Constant])],
    predicates          :: [PredRep],
    silent              :: Bool
  }
  deriving Typeable

instance Pretty Signature where
  pPrint sig = vcat (map prettyDecl decls)
    where
      decls = [(show (pPrint (app c [])), pPrintType (canonicalise (typ c))) | c <- constants sig, not (conIsBackground c)]
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
    Just ty
      | null (vars ty) -> ty
      | otherwise ->
        error $ "Default type is not ground: " ++ prettyShow ty

maxTermSize_ :: Signature -> Int
maxTermSize_ = fromMaybe 7 . maxTermSize

maxPruningSize_ :: Signature -> Int
maxPruningSize_ sig =
  max (fromMaybe 0 (maxPruningSize sig)) (maxTermSize_ sig)

maxCommutativeSize_ = fromMaybe 5 . maxCommutativeSize

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
defaultInstances = mconcat [
  inst (\(Dict :: Dict (Arbitrary A)) -> Dict :: Dict (Arbitrary [A])),
  inst (\(Dict :: Dict (Ord A)) -> Dict :: Dict (Ord [A])),
  inst (\(Dict :: Dict (CoArbitrary A)) -> Dict :: Dict (CoArbitrary [A])),
  inst (\(Dict :: Dict (Arbitrary A)) -> Dict :: Dict (Arbitrary (Maybe A))),
  inst (\(Dict :: Dict (Ord A)) -> Dict :: Dict (Ord (Maybe A))),
  inst (\(Dict :: Dict (CoArbitrary A)) -> Dict :: Dict (CoArbitrary (Maybe A))),
  baseType (undefined :: ()),
  baseType (undefined :: Int),
  baseType (undefined :: Integer),
  baseType (undefined :: Bool),
  baseType (undefined :: Char),
  inst (Dict :: Dict (CoArbitrary Int)),
  inst (Dict :: Dict (CoArbitrary Integer)),
  inst (Dict :: Dict (CoArbitrary Bool)),
  inst (Dict :: Dict (CoArbitrary Char)),
  inst (\(Dict :: Dict (CoArbitrary A)) (Dict :: Dict (Arbitrary B)) -> Dict :: Dict (Arbitrary (A -> B))),
  inst (\(Dict :: Dict (Arbitrary A)) (Dict :: Dict (CoArbitrary B)) -> Dict :: Dict (CoArbitrary (A -> B))),
  inst (\(Dict :: Dict (Ord A)) (Dict :: Dict (Ord B)) -> Dict :: Dict (Ord (A, B))),
  inst (\(Dict :: Dict (Arbitrary A)) (Dict :: Dict (Arbitrary B)) -> Dict :: Dict (Arbitrary (A, B))),
  inst (\(Dict :: Dict (CoArbitrary A)) (Dict :: Dict (CoArbitrary B)) -> Dict :: Dict (CoArbitrary (A, B))),
  inst (\(x :: A, (y :: B, z :: C)) -> (x, y, z)),
  inst (\(x :: A, (y :: B, (z :: C, w :: D))) -> (x, y, z, w)),
  inst (\(x :: A, (y :: B, (z :: C, (w :: D, v :: E)))) -> (x, y, z, w, v)),
  inst (\() -> Dict :: Dict ()),
  inst (\(dict :: Dict (Arbitrary A)) -> DictOf dict),
  names1 (\(NamesFor names :: NamesFor A) ->
            NamesFor (map (++ "s") names) :: NamesFor [A]),
  names (NamesFor ["x", "y", "z"] :: NamesFor Int),
  names (NamesFor ["x", "y", "z"] :: NamesFor Integer),
  names (NamesFor ["p", "q", "r"] :: NamesFor (A -> Bool)),
  names (NamesFor ["f", "g", "h"] :: NamesFor (A -> B)),
  names (NamesFor ["x", "y", "z"] :: NamesFor A),
  inst (\(dict :: Dict (Ord A)) -> return dict :: Gen (Dict (Ord A))),
  inst (\(dict :: Dict (Arbitrary A)) -> return dict :: Gen (Dict (Arbitrary A))),
  inst (\(dict :: Dict (CoArbitrary A)) -> return dict :: Gen (Dict (CoArbitrary A))),
  inst (\(Dict :: Dict (Arbitrary A)) -> arbitrary :: Gen A),
  inst (\(dict :: Dict (Ord A)) -> Observe dict return),
  inst (\(obs :: Observe A B) -> observeTraversable ins obs :: Observe [A] [B]),
  inst (\(Dict :: Dict (Arbitrary A),
          obs :: Observe B C) -> observeFunction obs :: Observe (A -> B) C ),
  inst (\(obs :: Observe A B) -> Observe1 (toValue obs))]

data Observe a b = Observe (Dict (Ord b)) (a -> Gen b) deriving Typeable
newtype Observe1 a = Observe1 (Value (Observe a)) deriving Typeable

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

newtype DictOf c a = DictOf { unDictOf :: Dict (c a) } deriving Typeable

instance Monoid Signature where
  mempty = Signature [] mempty [] Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing False Nothing Nothing [] [] False
  Signature cs is b th d s ps dp s1 t tim pr simp p pctxs prds sil `mappend` Signature cs' is' b' th' d' s' ps' dp' s1' t' tim' pr' simp' p' pctxs' prds' sil' =
    Signature (cs++cs') (is `mappend` is') (b++b')
      (th `mplus` th')
      (d `mplus` d')
      (s `mplus` s')
      (ps `mplus` ps')
      (dp `mplus` dp')
      (s1 `mplus` s1')
      (t `mplus` t')
      (tim `mplus` tim')
      (pr || pr')
      (simp `mplus` simp')
      (p `mplus` p')
      (pctxs `mplus` pctxs')
      (prds `mplus` prds')
      (sil || sil')

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
predicateSig sig = let ps             = predicates sig in
                       sig {constants = nub $ constants sig ++ (concatMap selectors ps) ++ map predCons ps ++ [constant "True" True | not (null ps)],
                            instances =
                               instances sig ++ map predInstances ps,
                            conditionalsContext = [(predCons p, selectors p) | p <- ps]
                           }
