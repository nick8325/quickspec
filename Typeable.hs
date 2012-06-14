-- A wrapper around Data.Typeable, to work around:
--   1) The lack of an Ord instance in older GHCs,
--   2) bug #5962 in new GHCs.

{-# LANGUAGE NoMonomorphismRestriction #-}
module Typeable(TypeRep, T.Typeable, T.Typeable1, T.Typeable2,
                typeOf, typeOf1, cast, mkTyConApp, typeRepTyCon,
                splitTyConApp, mkFunTy, unTypeRep) where

import qualified Data.Typeable as T
import Data.Ord

newtype TypeRep = TypeRep { unTypeRep :: T.TypeRep }

instance Eq TypeRep where
  ty == ty' =
    unTypeRep ty == unTypeRep ty' ||
    ty `compare` ty' == EQ

instance Ord TypeRep where
  compare = comparing splitTyConApp

instance Show TypeRep where
  showsPrec p = showsPrec p . unTypeRep 

typeOf = TypeRep . T.typeOf
typeOf1 = TypeRep . T.typeOf1
cast = T.cast

mkTyConApp f xs = TypeRep (T.mkTyConApp f (map unTypeRep xs))
typeRepTyCon = T.typeRepTyCon . unTypeRep
splitTyConApp ty = (c, map TypeRep tys)
  where (c, tys) = T.splitTyConApp (unTypeRep ty)
mkFunTy lhs rhs = TypeRep (T.mkFunTy (unTypeRep lhs) (unTypeRep rhs))

