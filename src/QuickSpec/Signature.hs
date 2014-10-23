-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, Rank2Types, StandaloneDeriving, TypeOperators, FlexibleContexts, KindSignatures, GeneralizedNewtypeDeriving, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module QuickSpec.Signature where

#include "errors.h"
import Prelude hiding (sequence)
import Data.Constraint
import QuickSpec.Base
import QuickSpec.Utils
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Prop
import Data.Functor.Identity
import Data.Monoid
import Test.QuickCheck hiding (subterms)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Char hiding (ord)
import Data.Maybe
import Data.List
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.Traversable hiding (mapM)
import Debug.Trace
import Control.Monad hiding (sequence)

newtype Instance = Instance (Value Instance1) deriving Show
newtype Instance1 a = Instance1 (Value (Instance2 a))
data Instance2 a b = Instance2 (b -> a)

instance Typed Instance where
  typ (Instance x) = typ x
  typeSubstA f (Instance x) =
    Instance <$> do
      y <- typeSubstA f x
      case unwrap y of
        Instance1 y `In` w -> do
          z <- typeSubstA f y
          return (wrap w (Instance1 z))

makeInstance :: forall a b. (Typeable a, Typeable b) => (b -> a) -> [Instance]
makeInstance f =
  case typeOf (undefined :: a) of
    Fun Arrow _ ->
      ERROR "makeInstance: curried functions not supported"
    _ ->
      [Instance (toValue (Instance1 (toValue (Instance2 f))))]

deriving instance Typeable Ord
deriving instance Typeable Arbitrary
deriving instance Typeable CoArbitrary
deriving instance Typeable (() :: Constraint)

data Signature =
  Signature {
    constants          :: [Constant],
    instances          :: [[Instance]],
    background         :: [Prop],
    defaultTo          :: Maybe Type,
    maxTermSize        :: Maybe Int,
    maxCommutativeSize :: Maybe Int,
    maxTests           :: Maybe Int,
    extraPruner        :: Maybe ExtraPruner }
  deriving (Show,Typeable)

instance Pretty Signature where
  pretty sig = vcat (map prettyDecl decls)
    where
      decls = [(show (pretty (Fun c [] :: Term)), pretty (typ c)) | c <- constants sig, not (conIsBackground c)]
      maxWidth = maximum (0:map (length . fst) decls)
      pad xs = replicate (maxWidth - length xs) ' ' ++ xs
      prettyDecl (name, ty) =
        hang (text (pad name) <+> text "::") 2 ty

defaultTo_ :: Signature -> Type
defaultTo_ sig =
  case defaultTo sig of
    Nothing -> typeOf (undefined :: Int)
    Just ty
      | null (vars ty) -> ty
      | otherwise ->
        error $ "Default type is not ground: " ++ prettyShow ty

maxTermSize_ :: Signature -> Int
maxTermSize_ = fromMaybe 9 . maxTermSize

maxCommutativeSize_ = fromMaybe 5 . maxCommutativeSize

maxTests_ :: Signature -> Int
maxTests_ = fromMaybe 100 . maxTests

data ExtraPruner = E Int | SPASS Int | Z3 Int | None deriving Show

extraPruner_ :: Signature -> ExtraPruner
extraPruner_ = fromMaybe (SPASS 1) . extraPruner

instances_ :: Signature -> [Instance]
instances_ sig = concat (instances sig ++ defaultInstances)

defaultInstances :: [[Instance]]
defaultInstances = [
  inst (Sub Dict :: Arbitrary A :- Arbitrary [A]),
  inst (Sub Dict :: Ord A :- Ord [A]),
  inst (Sub Dict :: CoArbitrary A :- CoArbitrary [A]),
  inst (Sub Dict :: Arbitrary A :- Arbitrary (Maybe A)),
  inst (Sub Dict :: Ord A :- Ord (Maybe A)),
  inst (Sub Dict :: CoArbitrary A :- CoArbitrary (Maybe A)),
  baseType (undefined :: Int),
  baseType (undefined :: Integer),
  baseType (undefined :: Bool),
  inst (Sub Dict :: () :- CoArbitrary Int),
  inst (Sub Dict :: () :- CoArbitrary Integer),
  inst (Sub Dict :: () :- CoArbitrary Bool),
  inst2 (Sub Dict :: (CoArbitrary A, Arbitrary B) :- Arbitrary (A -> B)),
  inst2 (Sub Dict :: (Arbitrary A, CoArbitrary B) :- CoArbitrary (A -> B)),
  makeInstance (\() -> Dict :: Dict ()),
  makeInstance (\(dict :: Dict (Arbitrary A)) -> DictOf dict),
  names1 (\(NamesFor names :: NamesFor A) ->
            NamesFor (map (++ "s") names) :: NamesFor [A]),
  names (NamesFor ["i", "j", "k"] :: NamesFor Int),
  names (NamesFor ["i", "j", "k"] :: NamesFor Integer),
  names (NamesFor ["p", "q", "r"] :: NamesFor (A -> Bool)),
  names (NamesFor ["f", "g", "h"] :: NamesFor (A -> B)),
  names (NamesFor ["x", "y", "z"] :: NamesFor A),
  makeInstance (\(dict :: Dict (Ord A)) -> Observe dict return),
  makeInstance (\(obs :: Observe A B) -> observeTraversable ins obs :: Observe [A] [B]),
  --makeInstance (\(Dict :: Dict (Arbitrary A),
  --                obs :: Observe B C) -> observeFunction obs :: Observe (A -> B) C ),
  makeInstance (\(obs :: Observe A B) -> Observe1 (toValue obs))]

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
  case findInstanceOf sig (skolemiseTypeVars ty) of
    (x:_) -> ofValue unNamesFor x

newtype NamesFor a = NamesFor { unNamesFor :: [String] } deriving Typeable
newtype DictOf c a = DictOf { unDictOf :: Dict (c a) } deriving Typeable

instance Monoid Signature where
  mempty = Signature [] [] [] Nothing Nothing Nothing Nothing Nothing
  Signature cs is b d s s1 t p `mappend` Signature cs' is' b' d' s' s1' t' p' =
    Signature (cs++cs') (is++is') (b++b')
      (d `mplus` d')
      (s `mplus` s')
      (s1 `mplus` s1')
      (t `mplus` t')
      (p `mplus` p')

signature :: Signature
signature = mempty

constant :: Typeable a => String -> a -> Constant
constant name x = Constant name value (poly value) ar style 1 False
  where
    value = toValue (Identity x)
    ar = arity (typeOf x)
    style
      | head name == ',' = Tuple ar
      | isOp name && ar >= 2 = Infix 5
      | otherwise = Curried

isOp :: String -> Bool
isOp "[]" = False
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_'

baseType :: forall a. (Ord a, Arbitrary a, Typeable a) => a -> [Instance]
baseType _ =
  mconcat [
    inst (Sub Dict :: () :- Ord a),
    inst (Sub Dict :: () :- Arbitrary a)]

baseTypeNames :: forall a. (Ord a, Arbitrary a, Typeable a) => [String] -> a -> [Instance]
baseTypeNames xs _ =
  mconcat [
    inst (Sub Dict :: () :- Ord a),
    inst (Sub Dict :: () :- Arbitrary a),
    names (NamesFor xs :: NamesFor a)]

inst :: forall c1 c2. (Typeable c1, Typeable c2) => c1 :- c2 -> [Instance]
inst ins = makeInstance f
  where
    f :: Dict c1 -> Dict c2
    f Dict = case ins of Sub dict -> dict

inst2 :: forall c1 c2 c3. (Typeable c1, Typeable c2, Typeable c3) => (c1, c2) :- c3 -> [Instance]
inst2 ins = makeInstance f
  where
    f :: (Dict c1, Dict c2) -> Dict c3
    f (Dict, Dict) = case ins of Sub dict -> dict

names  :: Typeable a => NamesFor a -> [Instance]
names x = makeInstance (\() -> x)

names1 :: (Typeable a, Typeable b) => (a -> NamesFor b) -> [Instance]
names1 = makeInstance

typeUniverse :: Signature -> Set Type
typeUniverse sig =
  Set.fromList $
    Var (TyVar 0):
    [ oneTypeVar (typ t) | c <- constants sig, t <- subterms' (typ c) ]
  where
    subterms' t = t:subterms1' t
    subterms1' (Fun Arrow [t, u]) = subterms' t ++ subterms1' u
    subterms1' (Fun _ ts) = concatMap subterms' ts
    subterms1' _ = []

bigTypeUniverse :: Signature -> Set Type
bigTypeUniverse sig =
  Set.fromList $
    Var (TyVar 0):
    [ oneTypeVar (typ t) | c <- constants sig, t <- subterms (typ c) ]

findInstanceOf :: forall f. Typeable f => Signature -> Type -> [Value f]
findInstanceOf sig ty =
  map (unwrapFunctor runIdentity) (findInstance sig ty')
  where
    ty' = typeRep (undefined :: proxy f) `applyType` ty

findInstance :: Signature -> Type -> [Value Identity]
findInstance sig (Fun unit [])
  | unit == tyCon () =
    return (toValue (Identity ()))
findInstance sig (Fun pair [ty1, ty2])
  | pair == tyCon ((),()) = do
    x <- findInstance sig ty1
    y <- findInstance sig ty2
    return (pairValues (liftA2 (,)) x y)
findInstance sig ty = do
  i <- instances_ sig
  let (i', ty') = unPoly (polyPair (poly i) (poly ty))
  sub <- maybeToList (unify (typ i') ty')
  let Instance i0 = typeSubst (evalSubst sub) i'
  withValue i0 $ \(Instance1 i1) -> do
    withValue i1 $ \(Instance2 f) -> do
      i2 <- findInstance sig (typ i1)
      sub <- maybeToList (match (typ i1) (typ i2))
      let Instance i0' = typeSubst (evalSubst sub) (Instance i0)
      case unwrap i0' of
        Instance1 i1' `In` w1 ->
          case unwrap i1' of
            Instance2 f `In` w2 ->
              return $! wrap w1 $! fmap f $! reunwrap w2 $! i2

newtype Name = Name String deriving Eq
instance Pretty Name where
  pretty (Name x) = text x

prettyRename :: Signature -> Prop -> PropOf (TermOf Name)
prettyRename sig p = fmap (rename (\x -> Map.findWithDefault __ x m)) p
  where
    vs = nub (concatMap vars (propTerms p))
    m = Map.fromList sub
    sub = evalState (mapM assign vs) Set.empty
    assign v = do
      s <- get
      let names = supply (namesFor_ sig (typ v))
          name = head (filter (`Set.notMember` s) names)
      modify (Set.insert name)
      return (v, Name name)
