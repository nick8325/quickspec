-- Signatures, collecting and finding witnesses, etc.
{-# LANGUAGE CPP, ConstraintKinds, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, Rank2Types, StandaloneDeriving, TypeOperators, FlexibleContexts, KindSignatures, GeneralizedNewtypeDeriving, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module QuickSpec.Instance where

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
