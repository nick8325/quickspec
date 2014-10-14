-- Imports the relevant parts of the term-rewriting package
-- and provides a few things on top.

{-# LANGUAGE CPP, TypeSynonymInstances #-}
module QuickSpec.Base(
  Tm,
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Term.Ops,
  module Data.Rewriting.Substitution, evalSubst, subst, substA, unifyMany,
  module QuickSpec.Pretty,
  module Text.PrettyPrint.HughesPJ) where

#include "errors.h"

import Data.Rewriting.Term hiding (Term, fold, map, fromString, parse, parseIO, parseFun, parseVar, parseWST)
import Data.Rewriting.Term.Ops(subterms)
import qualified Data.Rewriting.Term as T
import Data.Rewriting.Substitution hiding (apply, fromString, parse, parseIO)
import qualified Data.Rewriting.Substitution as T
import Control.Applicative
import Data.Traversable(sequenceA)
import qualified Data.Map as Map
import Data.Map(Map)
import QuickSpec.Pretty
import Text.PrettyPrint.HughesPJ

-- Renamings of functionality from term-rewriting.
type Tm = T.Term

foldTerm :: (v -> a) -> (f -> [a] -> a) -> Tm f v -> a
foldTerm = T.fold

mapTerm :: (f -> f') -> (v -> v') -> Tm f v -> Tm f' v'
mapTerm = T.map

evalSubst :: Ord v => Subst f v -> v -> Tm f v
evalSubst s = subst s . Var

subst :: Ord v => Subst f v -> Tm f v -> Tm f v
subst = T.apply

substA :: Applicative f => (v -> f (Tm c v)) -> Tm c v -> f (Tm c v)
substA s (Var x) = s x
substA s (Fun f xs) = Fun f <$> sequenceA (map (substA s) xs)

-- Unify several pairs of terms at once.
-- The first argument is a dummy function symbol which can be any
-- (non-bottom) value.
unifyMany :: (Eq f, Ord v) => f -> [(Tm f v, Tm f v)] -> Maybe (Subst f v)
unifyMany f xs = unify (Fun f (map fst xs)) (Fun f (map snd xs))

instance (Pretty f, Pretty v) => Pretty (Tm f v) where
  prettyPrec p (Var x) = prettyPrec p x
  prettyPrec p (Fun f xs) = prettyPrecApp p f xs
