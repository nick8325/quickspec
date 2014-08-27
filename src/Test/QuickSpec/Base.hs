-- Imports the relevant parts of the term-rewriting package
-- and provides a few basic abstractions on top.

{-# LANGUAGE CPP #-}
module Test.QuickSpec.Base(
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Substitution, subst,
  Apply(..), apply, canApply) where

#include "errors.h"

import Data.Rewriting.Term hiding (fold, map, fromString, parse, parseIO, parseFun, parseVar, parseWST)
import qualified Data.Rewriting.Term as T
import Data.Rewriting.Substitution hiding (apply, fromString, parse, parseIO)
import qualified Data.Rewriting.Substitution as T
import Data.Maybe

foldTerm :: (v -> a) -> (f -> [a] -> a) -> Term f v -> a
foldTerm = T.fold

mapTerm :: (f -> f') -> (v -> v') -> Term f v -> Term f' v'
mapTerm = T.map

subst :: Ord v => Subst f v -> Term f v -> Term f v
subst = T.apply

class Apply a where
  tryApply :: a -> a -> Maybe a

infixl `apply`
apply :: Apply a => a -> a -> a
apply f x =
  case tryApply f x of
    Nothing -> ERROR "apply: ill-typed term"
    Just y -> y

canApply :: Apply a => a -> a -> Bool
canApply f x = isJust (tryApply f x)
