-- Imports the relevant parts of the term-rewriting package
-- and provides a few basic abstractions on top.

{-# LANGUAGE CPP #-}
module Test.QuickSpec.Base(
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Substitution, subst, subst', unifyMany) where

#include "errors.h"

import Data.Rewriting.Term hiding (fold, map, fromString, parse, parseIO, parseFun, parseVar, parseWST)
import qualified Data.Rewriting.Term as T
import Data.Rewriting.Substitution hiding (apply, fromString, parse, parseIO)
import qualified Data.Rewriting.Substitution as T
import qualified Data.Rewriting.Substitution.Type as T
import Data.Maybe
import Data.Either
import qualified Data.Map as M
import Control.Monad

foldTerm :: (v -> a) -> (f -> [a] -> a) -> Term f v -> a
foldTerm = T.fold

mapTerm :: (f -> f') -> (v -> v') -> Term f v -> Term f' v'
mapTerm = T.map

subst :: Ord v => Subst f v -> Term f v -> Term f v
subst = T.apply

subst' :: (v -> Term f v) -> Term f v -> Term f v
subst' s (Var x) = s x
subst' s (Fun f xs) = Fun f (map (subst' s) xs)

unifyMany :: (Eq f, Ord v) => [(Term f v, Term f v)] -> Maybe (Subst f v)
unifyMany xs =
  case concat [ funs t ++ funs u | (t, u) <- xs ] of
    [] -> fmap hither (unifyWith () (thither xs))
    (f:_) -> unifyWith f xs
  where
    hither :: Subst () v -> Subst f v
    hither = T.fromMap . fmap castVar . T.toMap

    thither :: [(Term f v, Term f v)] -> [(Term () v, Term () v)]
    thither xs = [(castVar t, castVar u) | (t, u) <- xs ]

    castVar :: Term f v -> Term f' v
    castVar (Var x) = Var x

unifyWith :: (Eq f, Ord v) => f -> [(Term f v, Term f v)] -> Maybe (Subst f v)
unifyWith f xs = unify (Fun f (map fst xs)) (Fun f (map snd xs))
