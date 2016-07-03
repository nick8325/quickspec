-- Typed terms.
{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeSynonymInstances, FlexibleInstances #-}
module QuickSpec.Term(module QuickSpec.Term, module Twee.Term) where

import QuickSpec.Type
import qualified Twee.Term as Term
import Control.Monad
import Twee.Term(Numbered(..), build)
import Twee.Label

type Term f = Term.Term (Either f Type)

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
  Var (V ty x) = Term.App (Right ty) [build (Term.var (Term.V x))]

pattern App :: Numbered f => () => f -> [Term f] -> Term f
pattern App f ts = Term.App (Left f) ts

patVar :: Numbered f => Term f -> Maybe Var
patVar (Term.App (Right ty) [Term.Var (Term.V x)]) = Just (V ty x)
patVar _ = Nothing
