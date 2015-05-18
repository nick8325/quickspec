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
import QuickSpec.Base
import QuickSpec.Prop
import QuickSpec.Parse
import QuickSpec.Term
import QuickSpec.Type
import System.Timeout
import Test.QuickCheck hiding (subterms)
import Data.Ord
import Data.Rewriting.Substitution.Match
import {-# SOURCE #-} QuickSpec.Pruning.Completion(Completion)
import {-# SOURCE #-} QuickSpec.Pruning.Simple(SimplePruner)

newtype Instance = Instance (Value Instance1) deriving Show
newtype Instance1 a = Instance1 (Value (Instance2 a))
data Instance2 a b = Instance2 (b -> a)

instance Typed Instance where
  typ (Instance x) = typ x
  otherTypesDL (Instance x) =
    otherTypesDL x `mplus`
    case unwrap x of
      Instance1 y `In` _ -> typesDL y
  typeSubst sub (Instance x) =
    case unwrap (typeSubst sub x) of
      Instance1 y `In` w ->
        Instance (wrap w (Instance1 (typeSubst sub y)))

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
deriving instance Typeable Gen

type PrunerType = Completion

data Signature =
  Signature {
    constants          :: [Constant],
    instances          :: [[Instance]],
    background         :: [Prop],
    theory             :: Maybe PrunerType,
    defaultTo          :: Maybe Type,
    maxTermSize        :: Maybe Int,
    maxCommutativeSize :: Maybe Int,
    maxTests           :: Maybe Int,
    testTimeout        :: Maybe Int,
    simplify           :: Maybe (Signature -> Prop -> Prop),
    extraPruner        :: Maybe ExtraPruner }
  deriving Typeable

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
maxTermSize_ = fromMaybe 7 . maxTermSize

maxCommutativeSize_ = fromMaybe 5 . maxCommutativeSize

maxTests_ :: Signature -> Int
maxTests_ = fromMaybe 500 . maxTests

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
  baseType (undefined :: ()),
  baseType (undefined :: Int),
  baseType (undefined :: Integer),
  baseType (undefined :: Bool),
  baseType (undefined :: Char),
  inst (Sub Dict :: () :- CoArbitrary Int),
  inst (Sub Dict :: () :- CoArbitrary Integer),
  inst (Sub Dict :: () :- CoArbitrary Bool),
  inst (Sub Dict :: () :- CoArbitrary Char),
  inst2 (Sub Dict :: (CoArbitrary A, Arbitrary B) :- Arbitrary (A -> B)),
  inst2 (Sub Dict :: (Arbitrary A, CoArbitrary B) :- CoArbitrary (A -> B)),
  inst2 (Sub Dict :: (Ord A, Ord B) :- Ord (A, B)),
  inst2 (Sub Dict :: (Arbitrary A, Arbitrary B) :- Arbitrary (A, B)),
  inst2 (Sub Dict :: (CoArbitrary A, CoArbitrary B) :- CoArbitrary (A, B)),
  makeInstance (\(x :: A, (y :: B, z :: C)) -> (x, y, z)),
  makeInstance (\(x :: A, (y :: B, (z :: C, w :: D))) -> (x, y, z, w)),
  makeInstance (\(x :: A, (y :: B, (z :: C, (w :: D, v :: E)))) -> (x, y, z, w, v)),
  makeInstance (\() -> Dict :: Dict ()),
  makeInstance (\(dict :: Dict (Arbitrary A)) -> DictOf dict),
  names1 (\(NamesFor names :: NamesFor A) ->
            NamesFor (map (++ "s") names) :: NamesFor [A]),
  names (NamesFor ["i", "j", "k"] :: NamesFor Int),
  names (NamesFor ["i", "j", "k"] :: NamesFor Integer),
  names (NamesFor ["p", "q", "r"] :: NamesFor (A -> Bool)),
  names (NamesFor ["f", "g", "h"] :: NamesFor (A -> B)),
  names (NamesFor ["x", "y", "z"] :: NamesFor A),
  makeInstance (\(dict :: Dict (Ord A)) -> return dict :: Gen (Dict (Ord A))),
  makeInstance (\(Dict :: Dict (Arbitrary A)) -> arbitrary :: Gen A),
  makeInstance (\(dict :: Dict (Ord A)) -> Observe dict return),
  makeInstance (\(obs :: Observe A B) -> observeTraversable ins obs :: Observe [A] [B]),
  makeInstance (\(Dict :: Dict (Arbitrary A),
                 obs :: Observe B C) -> observeFunction obs :: Observe (A -> B) C ),
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
  mempty = Signature [] [] [] Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing
  Signature cs is b th d s s1 t tim simp p `mappend` Signature cs' is' b' th' d' s' s1' t' tim' simp' p' =
    Signature (cs++cs') (is++is') (b++b')
      (th `mplus` th')
      (d `mplus` d')
      (s `mplus` s')
      (s1 `mplus` s1')
      (t `mplus` t')
      (tim `mplus` tim')
      (simp `mplus` simp')
      (p `mplus` p')

signature :: Signature
signature = mempty

renumber :: Signature -> Signature
-- TODO get rid of this, use old-style API ("single constant" signature+monoid) instead
renumber sig =
  sig { constants = cs, background = map (fmap (mapTerm find id)) (background sig) }
  where
    cs =
      [ c | c <- constants sig, conIndex c /= 0 ] ++
      zipWith f (sortBy (comparing conName) [ c | c <- constants sig, conIndex c == 0 ])
                [succ (maximum (0:map conIndex (constants sig)))..]
    f c n = c { conIndex = n }
    find c | conIndex c == 0 = f c (head [ conIndex c' | c' <- cs, conName c == conName c' ])
           | otherwise = c

constant :: Typeable a => String -> a -> Constant
constant name x = Constant 0 name value (poly value) 0 style 1 False
  where
    value = toValue (Identity x)
    ar = arity (typeOf x)
    style
      | name == "()" = Tuple 0
      | take 1 name == "," = Tuple ar
      | take 2 name == "(," = Tuple ar
      | isOp name && ar >= 2 = Infix 5
      | isOp name = Prefix
      | otherwise = Curried

isOp :: String -> Bool
isOp "[]" = False
isOp xs | all (== '.') xs = True
isOp xs = not (all isIdent xs)
  where
    isIdent x = isAlphaNum x || x == '\'' || x == '_' || x == '.'

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

inst3 :: forall c1 c2 c3 c4. (Typeable c1, Typeable c2, Typeable c3, Typeable c4) => (c1, c2, c3) :- c4 -> [Instance]
inst3 ins = makeInstance f
  where
    f :: (Dict c1, Dict c2, Dict c3) -> Dict c4
    f (Dict, Dict, Dict) = case ins of Sub dict -> dict

inst4 :: forall c1 c2 c3 c4 c5. (Typeable c1, Typeable c2, Typeable c3, Typeable c4, Typeable c5) => (c1, c2, c3, c4) :- c5 -> [Instance]
inst4 ins = makeInstance f
  where
    f :: (Dict c1, Dict c2, Dict c3, Dict c4) -> Dict c5
    f (Dict, Dict, Dict, Dict) = case ins of Sub dict -> dict

inst5 :: forall c1 c2 c3 c4 c5 c6. (Typeable c1, Typeable c2, Typeable c3, Typeable c4, Typeable c5, Typeable c6) => (c1, c2, c3, c4, c5) :- c6 -> [Instance]
inst5 ins = makeInstance f
  where
    f :: (Dict c1, Dict c2, Dict c3, Dict c4, Dict c5) -> Dict c6
    f (Dict, Dict, Dict, Dict, Dict) = case ins of Sub dict -> dict

names  :: Typeable a => NamesFor a -> [Instance]
names x = makeInstance (\() -> x)

names1 :: (Typeable a, Typeable b) => (a -> NamesFor b) -> [Instance]
names1 = makeInstance

typeUniverse :: Signature -> Set Type
typeUniverse sig =
  Set.fromList $
    Var (TyVar 0):
    concatMap collapse
      [ oneTypeVar (typ t) | c <- constants sig, not (isId c), t <- types (typ c) ]
  where
    types t = typeRes t:typeArgs t ++ concatMap types (typeArgs t)
    collapse ty@(Fun f tys) =
      Var (TyVar 0):ty:
      map (Fun f) (mapM collapse tys)
    collapse (Var x) = [Var x]

data TypeKind = Useless | Partial | Useful deriving (Eq, Show)

typeKind :: Signature -> Type -> TypeKind
typeKind sig ty
  | occurs ty = Useful
  | any occurs (suffixes ty) = Partial
  | otherwise = Useless
  where
    suffixes t@(Fun Arrow [_, u]) = t:suffixes u
    suffixes t = [t]
    occurs t = or [ isJust (match t u) | u <- Set.toList u ]
    u = typeUniverse sig

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
    vs = nub (vars p)
    m = Map.fromList sub
    sub = evalState (mapM assign vs) Set.empty
    assign v = do
      s <- get
      let names = supply (namesFor_ sig (typ v))
          name = head (filter (`Set.notMember` s) names)
      modify (Set.insert name)
      return (v, Name name)

addBackground :: [String] -> Signature -> Signature
addBackground props sig =
  sig { background = background sig ++ map (parseProp (constants sig)) props }

printTheory :: Signature -> IO ()
printTheory sig = putStrLn (showTheory (background sig))
