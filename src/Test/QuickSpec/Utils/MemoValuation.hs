-- | Memoise the variable valuation function for terms.
--   In its own module because it's packed full of dangerous features!

{-# LANGUAGE Rank2Types #-}
module Test.QuickSpec.Utils.MemoValuation where

import Test.QuickSpec.Term
import Test.QuickSpec.Signature
import Data.Array hiding (index)
import Data.Array.Base(unsafeAt)
import Unsafe.Coerce
import GHC.Prim
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.TypeRel

memoValuation :: Sig -> Valuation -> Valuation
memoValuation sig (Valuation f) = Valuation (unsafeCoerce . unsafeAt arr . index . sym . unVariable)
  where arr :: Array Int Any
        arr = array (0, maximum (0:map (some (index . sym . unVariable)) vars))
                [(index (sym (unVariable v)), unsafeCoerce (f v))
                | Some v <- vars ]
        vars = toList (variables sig)