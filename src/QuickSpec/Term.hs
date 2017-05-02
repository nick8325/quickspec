-- Typed terms.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Base) where

import QuickSpec.Type
import qualified Twee.Base as Base
import Control.Monad
import Twee.Base hiding (Symbolic, Term, TermList, Builder, pattern Var, pattern App, Var(..), var, app, funs, vars, occ, occVar, isApp, isVar, subterms, subtermsList, properSubterms)
import qualified Data.DList as DList
import Twee.Label

type Symbolic f a = (Base.Symbolic a, ConstantOf a ~ Either f Type, Typeable f, Ord f)
type Term f = Base.Term (Either f Type)
type TermList f = Base.TermList (Either f Type)
type Builder f = Base.Builder (Either f Type)

data Var = V { var_ty :: Type, var_id :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show)

instance Typed Var where
  typ x = var_ty x
  otherTypesDL _ = mzero
  typeSubst_ sub (V ty x) = V (typeSubst_ sub ty) x

pattern Var :: (Ord f, Typeable f) => Var -> Term f
pattern Var x <- (patVar -> Just x) where

var :: (Ord f, Typeable f) => Var -> Builder f
var (V ty x) = Base.app (fun (Right ty) [build (Base.var (Base.V x))])

pattern App :: (Ord f, Typeable f) => f -> [Term f] -> Term f
pattern App f ts <- Base.App (fun_value -> Left f) (unpack -> ts)

app :: (Ord f, Typeable f, Build a, BuildFun a ~ Either f Type) => f -> [Term f] -> Builder f
app f ts = build (app (fun (Left f)) ts)

patVar :: (Ord f, Typeable f) => Term f -> Maybe Var
patVar (Base.App f (Cons (Base.Var (Base.V x)) Empty))
  | Right ty <- fun_value f = Just (V ty x)
patVar _ = Nothing

funs :: Symbolic f a => a -> [f]
funs x = [ f | t <- terms x, App f _ <- subtermsList t ]

vars :: Symbolic f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subtermsList t ]

occ :: Symbolic f a => f -> a -> Int
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
