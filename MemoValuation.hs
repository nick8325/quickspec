{-# LANGUAGE Rank2Types #-}
module MemoValuation where

import Term
import Signature
import Data.Array hiding (index)
import Unsafe.Coerce
import GHC.Prim
import Typed
import TypeRel

memoValuation :: Sig -> (forall a. Variable a -> a) -> (forall a. Variable a -> a)
memoValuation sig f = unsafeCoerce . (arr !) . index . sym . unVariable
  where arr :: Array Int Any
        arr = array (0, maximum (0:map (some (index . sym . unVariable)) vars))
                [(index (sym (unVariable v)), unsafeCoerce (f v))
                | Some v <- vars ]
        vars = TypeRel.toList (variables sig)