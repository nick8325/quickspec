-- Typed terms.
{-# LANGUAGE RecordWildCards, PatternSynonyms, CPP #-}
module QuickSpec.Term where

#include "errors.h"
import qualified Data.IntMap.Strict as Map
import Data.IntMap(IntMap)
import QuickSpec.Type
import qualified Twee.Base as Twee
import Twee.Base hiding (Term)
import Control.Monad

data Term f =
  Term {
    term    :: Twee.Term f,
    context :: IntMap Type }

instance (Typed f, Numbered f) => Typed (Term f) where
  typ Term{..} =
    case term of
      Var (MkVar x) ->
        Map.findWithDefault __ x context
      -- the type of a constant should assume it's been applied
      App f _ -> typ f

  otherTypesDL Term{..} =
    msum [return (typ (Term t context)) | t <- properSubterms term] `mplus`
    msum (map return (Map.elems context))

  typeReplace sub Term{..} =
    Term {
      term    = build (mapFun (toFun . typeReplace sub . fromFun) term),
      context = fmap (typeReplace sub) context }
