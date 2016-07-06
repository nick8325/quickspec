-- Typed terms.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Base) where

import QuickSpec.Type
import qualified Twee.Base as Base
import Control.Monad
import Twee.Base hiding (Term, TermList, pattern Var, pattern Fun, Var(..), funs, vars, occ, occVar, isFun, isVar, subterms, subtermsList, properSubterms, properSubtermsList)
import qualified Data.DList as DList
import Twee.Label

type Symb f a = (Symbolic a, ConstantOf a ~ ConstantOf (Term f), Labelled f, Eq f)
type Term f = Base.Term (Either f Type)
type TermList f = Base.TermList (Either f Type)

instance Labelled Type where cache = typeCache
{-# NOINLINE typeCache #-}
typeCache :: Cache Type
typeCache = mkCache

data Var = V { var_ty :: Type, var_idx :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show)

instance Typed Var where
  typ x = var_ty x
  otherTypesDL _ = mzero
  typeReplace sub (V ty x) = V (typeReplace sub ty) x

pattern Var :: Labelled f => () => Var -> Term f
pattern Var x <- (patVar -> Just x) where
  Var (V ty x) = build (fun (F (2*label ty+1) (Right ty)) [build (Base.var (Base.V x))])

pattern Fun :: Labelled f => () => f -> [Term f] -> Term f
pattern Fun f ts <- Base.Fun (F _ (Left f)) (unpack -> ts) where
  Fun f ts = build (fun (F (2*label f) (Left f)) ts)

patVar :: Labelled f => Term f -> Maybe Var
patVar (Base.Fun (F _ (Right ty)) (Cons (Base.Var (Base.V x)) Empty)) =
  Just (V ty x)
patVar _ = Nothing

funs :: Symb f a => a -> [f]
funs x = [ f | t <- terms x, Fun f _ <- subtermsList t ]

vars :: Symb f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subtermsList t ]

occ :: Symb f a => f -> a -> Int
occ x t = length (filter (== x) (funs t))

occVar :: Symb f a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

isFun :: Labelled f => Term f -> Bool
isFun Fun{} = True
isFun _ = False

isVar :: Labelled f => Term f -> Bool
isVar Var{} = True
isVar _ = False

subterms :: Labelled f => Term f -> [Term f]
subterms = subtermsList . singleton

subtermsList :: Labelled f => TermList f -> [Term f]
subtermsList = filter (not . Base.isVar) . Base.subtermsList

properSubterms :: Labelled f => Term f -> [Term f]
properSubterms = properSubtermsList . singleton

properSubtermsList :: Labelled f => TermList f -> [Term f]
properSubtermsList = filter (not . Base.isVar) . Base.properSubtermsList

instance (Labelled f, Typed f) => Typed (Term f) where
  typ (Var x) = var_ty x
  typ (Fun f _) = typ f
  otherTypesDL t =
    DList.fromList (map fromFun (Base.funs t)) >>= typesDL

  typeReplace sub (Var x) = Var x { var_ty = typeReplace sub (var_ty x) }
  typeReplace sub (Fun f ts) = Fun (typeReplace sub f) (typeReplace sub ts)
