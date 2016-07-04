-- Typed terms.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances, TypeFamilies, ConstraintKinds #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Base) where

import QuickSpec.Type
import qualified Twee.Base as Base
import Control.Monad
import Twee.Base hiding (Term, TermList, pattern App, pattern Var, Var(..), vars, occVar, isVar, subterms, subtermsList, properSubterms, properSubtermsList)
import Twee.Label
import qualified Data.DList as DList

type Symb f a = (Symbolic a, ConstantOf a ~ ConstantOf (Term f), Numbered f)
type Term f = Base.Term (Either f Type)
type TermList f = Base.TermList (Either f Type)

instance Numbered Type where toInt = label
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

pattern Var :: Numbered f => () => Var -> Term f
pattern Var x <- (patVar -> Just x) where
  Var (V ty x) = Base.App (Right ty) [build (Base.var (Base.V x))]

pattern App :: Numbered f => () => f -> [Term f] -> Term f
pattern App f ts = Base.App (Left f) ts

patVar :: Numbered f => Term f -> Maybe Var
patVar (Base.App (Right ty) [Base.Var (Base.V x)]) = Just (V ty x)
patVar _ = Nothing

vars :: Symb f a => a -> [Var]
vars x = [ v | t <- terms x, Var v <- subtermsList t ]

occVar :: Symb f a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

isVar :: Numbered f => Term f -> Bool
isVar Var{} = True
isVar _ = False

subterms :: Numbered f => Term f -> [Term f]
subterms = subtermsList . singleton

subtermsList :: Numbered f => TermList f -> [Term f]
subtermsList = filter (not . Base.isVar) . Base.subtermsList

properSubterms :: Numbered f => Term f -> [Term f]
properSubterms = properSubtermsList . singleton

properSubtermsList :: Numbered f => TermList f -> [Term f]
properSubtermsList = filter (not . Base.isVar) . Base.properSubtermsList

instance (Numbered f, Typed f) => Typed (Term f) where
  typ (Var x) = var_ty x
  typ (App f _) = typ f
  otherTypesDL t =
    DList.fromList (map fromFun (Base.funs t)) >>= typesDL

  typeReplace sub (Var x) = Var x { var_ty = typeReplace sub (var_ty x) }
  typeReplace sub (App f ts) = App (typeReplace sub f) (typeReplace sub ts)
