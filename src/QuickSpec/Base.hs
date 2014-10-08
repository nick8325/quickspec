-- Imports the relevant parts of the term-rewriting package
-- and provides a few things on top.

{-# LANGUAGE CPP #-}
module QuickSpec.Base(
  Tm,
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Substitution, evalSubst, subst, substA, unifyMany,
  module Text.PrettyPrint.ANSI.Leijen, prettyPrint, prettyShow) where

#include "errors.h"

import Data.Rewriting.Term hiding (Term, fold, map, fromString, parse, parseIO, parseFun, parseVar, parseWST)
import qualified Data.Rewriting.Term as T
import Data.Rewriting.Substitution hiding (apply, fromString, parse, parseIO)
import qualified Data.Rewriting.Substitution as T
import Control.Applicative
import Data.Traversable(sequenceA)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Data.Map as Map
import Data.Map(Map)

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

prettyPrint :: Pretty a => a -> IO ()
prettyPrint x = putStrLn (prettyShow x)

prettyShow :: Pretty a => a -> String
prettyShow x = displayS (renderSmart 0.4 100 (pretty x)) ""

instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pretty m =
    braces (align (sep (punctuate comma (map binding (Map.toList m)))))
    where
      binding (x, v) = pretty x <> text ":" <> pretty v
