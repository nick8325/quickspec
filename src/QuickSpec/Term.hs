-- Typed terms.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds, DeriveGeneric, DeriveAnyClass #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Base) where

import QuickSpec.Type
import qualified Twee.Base as Base
import Control.Monad
import Twee.Base hiding (Symbolic, Term, TermList, Builder, pattern Var, pattern App, Var(..), Fun, F, fun, fun_value, var, funs, vars, occ, occVar, isApp, isVar, subterms, subtermsList, properSubterms)
import qualified Data.DList as DList
import Twee.Label
import GHC.Generics
import Test.QuickCheck(CoArbitrary)

type Symbolic f a = (Base.Symbolic a, ConstantOf a ~ Either f Type, Typeable f, Ord f)
type Term f = Base.Term (Either f Type)
type TermList f = Base.TermList (Either f Type)
type Builder f = Base.Builder (Either f Type)
type Fun f = Base.Fun (Either f Type)

data Var = V { var_ty :: Type, var_id :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show, Generic, CoArbitrary)

instance Typed Var where
  typ x = var_ty x
  otherTypesDL _ = mzero
  typeSubst_ sub (V ty x) = V (typeSubst_ sub ty) x

var :: (Ord f, Typeable f) => Var -> Builder f
var (V ty x) = Base.app (Base.fun (Right ty)) (Base.var (Base.V x))

fun :: (Ord f, Typeable f) => f -> Fun f
fun = Base.fun . Left

fun_value :: Fun f -> f
fun_value f =
  case Base.fun_value f of
    Left x -> x
    Right _ -> error "type tag used as Fun"

pattern F :: f -> Fun f
pattern F x <- (fun_value -> x)

pattern Var :: Var -> Term f
pattern Var x <- (patVar -> Just x)

patVar :: Term f -> Maybe Var
patVar (Base.App (Base.F (Right ty)) (Cons (Base.Var (Base.V x)) Empty)) =
  Just (V ty x)
patVar _ = Nothing

pattern App :: Fun f -> TermList f -> Term f
pattern App f ts <- (patApp -> Just (f, ts))

patApp :: Term f -> Maybe (Fun f, TermList f)
patApp (Base.App f@(Base.F (Left _)) ts) = Just (f, ts)
patApp _ = Nothing

funs :: Symbolic f a => a -> [Fun f]
funs x = [ f | t <- terms x, App f _ <- subtermsList t ]

vars :: Symbolic f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subtermsList t ]

occ :: Symbolic f a => Fun f -> a -> Int
occ x t = length (filter (== x) (funs t))

occVar :: Symbolic f a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

isApp :: (Ord f, Typeable f) => Term f -> Bool
isApp App{} = True
isApp _ = False

isVar :: (Ord f, Typeable f) => Term f -> Bool
isVar Var{} = True
isVar _ = False

subterms :: (Ord f, Typeable f) => Term f -> [Term f]
subterms = subtermsList . singleton

subtermsList :: (Ord f, Typeable f) => TermList f -> [Term f]
subtermsList = filter (not . Base.isVar) . Base.subtermsList

properSubterms :: (Ord f, Typeable f) => Term f -> [Term f]
properSubterms = filter (not . Base.isVar) . Base.properSubterms

evaluateTerm :: Apply a =>
  (fun -> a) -> (Var -> a) -> Term fun -> a
evaluateTerm fun var = eval
  where
    eval (Var x) = var x
    eval (App (F f) ts) =
      foldl apply (fun f) (map eval (unpack ts))
