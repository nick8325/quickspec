{-# LANGUAGE CPP #-}
module Test.QuickSpec.Pruning where

#include "errors.h"
import Test.QuickSpec.Base
import Test.QuickSpec.Type
import Test.QuickSpec.Term
import Test.QuickSpec.Equation
import Data.Rewriting.Substitution.Type
import qualified Data.Map as Map
import Data.Maybe
import Control.Monad.Trans.State.Strict

class Pruner a where
  emptyPruner :: a
  unifyUntyped :: PruningTerm -> PruningTerm -> State a Bool
  repUntyped :: PruningTerm -> State a (Maybe PruningTerm)

unify :: Pruner a => Typed Equation -> State a Bool
unify e = unifyUntyped (encodeTypes (lhs e)) (encodeTypes (rhs e))

rep :: Pruner a => Typed Term -> State a (Maybe Term)
rep t = fmap (fmap decodeTypes) (repUntyped (encodeTypes t))

type PruningTerm = Tm PruningConstant PruningVariable

data PruningConstant
  = TermConstant Constant
  | TypeConstant TyCon
  | HasType
  deriving (Eq, Ord, Show)

instance Pretty PruningConstant where
  pretty (TermConstant x) = pretty x
  pretty (TypeConstant x) = pretty x
  pretty HasType = text "@"

data PruningVariable
  = TermVariable Variable
  | TypeVariable TyVar
  deriving (Eq, Ord, Show)

instance Pretty PruningVariable where
  pretty (TermVariable x) = pretty x
  pretty (TypeVariable x) = pretty x

encodeTypes :: Typed Term -> PruningTerm
encodeTypes t = subst s' u
  where
    s' =
      fromMap
        (Map.mapKeysMonotonic TypeVariable
          (fmap injectType (toMap s)))
    Just (u, s) =
      runUnifyM (freshTyVarFor (untyped t)) (addTags (untyped t))
    injectType = mapTerm TypeConstant TypeVariable
    addTags t = fmap tag (findType t)
    tag (t, ty) = Fun HasType [injectType ty, t]

    findType (Var x) =
      return (Var (TermVariable x),
              fromMaybe __ (Map.lookup x (context t)))
    findType (Fun f xs) = do
      args <- mapM findType xs
      res <- fmap Var freshTyVar
      fty <- freshenM (valueType (conValue f))
      equalise fty (arrowType (map snd args) res)
      return (Fun (TermConstant f) (map tag args), res)

decodeTypes :: PruningTerm -> Term
decodeTypes (Fun HasType [_, Var (TermVariable x)]) = Var x
decodeTypes (Fun HasType [_, Fun (TermConstant f) xs]) =
  Fun f (map decodeTypes xs)
