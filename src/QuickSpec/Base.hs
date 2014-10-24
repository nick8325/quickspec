-- Imports the relevant parts of the term-rewriting package
-- and provides a few things on top.

{-# LANGUAGE CPP, TypeSynonymInstances #-}
module QuickSpec.Base(
  Tm,
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Term.Ops,
  module Data.Rewriting.Substitution, evalSubst, subst, substA, unifyMany,
  module QuickSpec.Pretty,
  module Text.PrettyPrint.HughesPJ,
  PrettyTerm(..), TermStyle(..), prettyStyle) where

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

class Pretty a => PrettyTerm a where
  termStyle :: a -> TermStyle
  termStyle _ = Uncurried

data TermStyle = Curried | Uncurried | Tuple Int | TupleType | ListType | Infix Int | Infixr Int | Prefix | Postfix | Gyrator deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Tm f v) where
  prettyPrec p (Var x) = prettyPrec p x
  prettyPrec p (Fun f xs) =
    prettyStyle (termStyle f) p (pretty f) xs

prettyStyle Curried p d [] = d
prettyStyle Curried p d xs =
  prettyParen (p > 10) $
    hang d 2
      (fsep (map (prettyPrec 11) xs))
prettyStyle Uncurried p d [] = d
prettyStyle Uncurried p d xs =
  d <> parens (fsep (punctuate comma (map pretty xs)))
prettyStyle (Tuple arity) p d xs
  | length xs >= arity =
    prettyStyle Curried p
      (prettyTuple (take arity (map pretty xs)))
      (drop arity xs)
  | otherwise =
    prettyStyle Curried p
      (text ("(" ++ replicate arity ',' ++ ")")) xs
prettyStyle Postfix p d [x] =
  prettyPrec 11 x <> d
prettyStyle Postfix p d xs =
  prettyStyle Curried p (parens d) xs
prettyStyle Prefix p d [x] =
  d <> prettyPrec 11 x
prettyStyle Prefix p d xs =
  prettyStyle Curried p (parens d) xs
prettyStyle TupleType p d xs =
  prettyStyle (Tuple (length xs)) p d xs
prettyStyle ListType p d [x] =
  brackets (pretty x)
prettyStyle ListType p d xs =
  prettyStyle Curried p d xs
prettyStyle Gyrator p d [x, y] =
  d <> brackets (sep (punctuate comma [pretty x, pretty y]))
prettyStyle Gyrator p d (x:y:zs) =
  prettyStyle Curried p (prettyStyle Gyrator p d [x, y]) zs
prettyStyle Gyrator p d xs = prettyStyle Curried p d xs
prettyStyle style p d xs =
  case xs of
    [x, y] ->
      prettyParen (p > pOp) $
        hang (prettyPrec (pOp+1) x <+> d) 2
             (prettyPrec (pOp+r) y)
    _ ->
      prettyParen (p > pOp) $
        hang (parens d) 2
          (fsep (map (prettyPrec 11) xs))
  where
    (r, pOp) =
      case style of
        Infixr pOp -> (0, pOp)
        Infix  pOp -> (1, pOp)
