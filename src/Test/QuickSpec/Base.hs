-- Imports the relevant parts of the term-rewriting package
-- and provides a few basic abstractions on top.

{-# LANGUAGE CPP #-}
module Test.QuickSpec.Base(
  Tm(..),
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Substitution, subst, subst', unifyMany) where

#include "errors.h"

import Data.Rewriting.Term hiding (Term, fold, map, fromString, parse, parseIO, parseFun, parseVar, parseWST)
import qualified Data.Rewriting.Term as T
import Data.Rewriting.Substitution hiding (apply, fromString, parse, parseIO)
import qualified Data.Rewriting.Substitution as T
import qualified Data.Rewriting.Substitution.Type as T
import Data.Maybe
import Data.Either
import qualified Data.Map as M
import Control.Monad

type Tm = T.Term

foldTerm :: (v -> a) -> (f -> [a] -> a) -> Tm f v -> a
foldTerm = T.fold

mapTerm :: (f -> f') -> (v -> v') -> Tm f v -> Tm f' v'
mapTerm = T.map

subst :: Ord v => Subst f v -> Tm f v -> Tm f v
subst = T.apply

subst' :: (v -> Tm f v) -> Tm f v -> Tm f v
subst' s (Var x) = s x
subst' s (Fun f xs) = Fun f (map (subst' s) xs)

unifyMany :: (Eq f, Ord v) => [(Tm f v, Tm f v)] -> Maybe (Subst f v)
unifyMany xs =
  case concat [ funs t ++ funs u | (t, u) <- xs ] of
    [] -> fmap hither (unifyWith () (thither xs))
    (f:_) -> unifyWith f xs
  where
    hither :: Subst () v -> Subst f v
    hither = T.fromMap . fmap castVar . T.toMap

    thither :: [(Tm f v, Tm f v)] -> [(Tm () v, Tm () v)]
    thither xs = [(castVar t, castVar u) | (t, u) <- xs ]

    castVar :: Tm f v -> Tm f' v
    castVar (Var x) = Var x

unifyWith :: (Eq f, Ord v) => f -> [(Tm f v, Tm f v)] -> Maybe (Subst f v)
unifyWith f xs = unify (Fun f (map fst xs)) (Fun f (map snd xs))
