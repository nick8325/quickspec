-- New plan:
-- simple type of terms like in pre-twee QS.
-- Parametrised on constants and variables.
-- On second thoughts, just introduce term type first.
-- Then reintroduce schemas, then proper parametrisation
-- (and maybe not just on constant type - on term type).

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

-- Twee terms are untyped.
-- So we pair a Twee term with a context, a map from variable to type.
data Term f =
  Term {
    tm_term :: Twee.Term f,
    tm_ctx  :: IntMap Type }

instance (Typed f, Numbered f) => Typed (Term f) where
  typ Term{..} =
    case tm_term of
      Var (MkVar x) ->
        Map.findWithDefault __ x tm_ctx
      App f _ -> typ f

  otherTypesDL Term{..} =
    msum [return (typ (Term t tm_ctx)) | t <- properSubterms tm_term] `mplus`
    msum (map return (Map.elems tm_ctx))

  typeReplace sub Term{..} =
    Term {
      term    = build (mapFun (toFun . typeReplace sub . fromFun) tm_term),
      context = fmap (typeReplace sub) tm_ctx }

instance Symbolic (Term f) where
  type ConstantOf (Term f) = f
  term Term{..} = tm_term
  termsDL = return . tm_term
  replace sub (Term t ctx) = Term (replace sub t) ctx
  -- XXXXX oh no!
  -- substitution doesn't respect types!
  -- Need our own QuickSpec-symbolic class.
  -- Or just have our own typed-term type without twee.
