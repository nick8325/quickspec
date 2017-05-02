-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, Rank2Types, StandaloneDeriving, TypeOperators, FlexibleContexts, KindSignatures, GeneralizedNewtypeDeriving, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module QuickSpec.Instance where

#include "errors.h"
import Test.QuickCheck
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
import QuickSpec.Prop
import QuickSpec.Parse
import QuickSpec.Term
import QuickSpec.Type
import Data.Ord
import {-# SOURCE #-} QuickSpec.Pruning.Completion(Completion)
import {-# SOURCE #-} QuickSpec.Pruning.Simple(SimplePruner)
import Twee.Base
import qualified Twee.Label as Label

newtype Instance = Instance (Value Instance1) deriving Show
newtype Instance1 a = Instance1 (Value (Instance2 a))
data Instance2 a b = Instance2 (b -> a)

instance Typed Instance where
  typ (Instance x) = typ x
  otherTypesDL (Instance x) =
    otherTypesDL x `mplus`
    case unwrap x of
      Instance1 y `In` _ -> typesDL y
  typeReplace sub (Instance x) =
    case unwrap (typeReplace sub x) of
      Instance1 y `In` w ->
        Instance (wrap w (Instance1 (typeReplace sub y)))

makeInstance :: forall a b. (Typeable a, Typeable b) => (b -> a) -> [Instance]
makeInstance f =
  case typeOf (undefined :: a) of
    App Arrow _ ->
      ERROR("makeInstance: curried functions not supported")
    _ ->
      [Instance (toValue (Instance1 (toValue (Instance2 f))))]

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

newtype NamesFor a = NamesFor { unNamesFor :: [String] } deriving Typeable

names  :: Typeable a => NamesFor a -> [Instance]
names x = makeInstance (\() -> x)

names1 :: (Typeable a, Typeable b) => (a -> NamesFor b) -> [Instance]
names1 = makeInstance
