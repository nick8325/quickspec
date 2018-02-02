-- | The main QuickSpec module.
--
-- For many examples of use, see the @examples@ directory in the source distribution,
-- which you can also find at <https://github.com/nick8325/quickspec/blob/master/examples>.
module QuickSpec(
  -- * Running QuickSpec
  quickSpec,
  quickSpecWithBackground,
  signature,
  Signature(..),
  -- * Declaring functions and predicates
  constant,
  predicate,
  -- * Type variables for declaring polymorphic functions
  A, B, C, D, E,
  -- * Declaring new types
  baseType,
  baseTypeNames,
  inst,
  observe,
  names, NamesFor(..)) where

import QuickSpec.Eval
import QuickSpec.Parse
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Pruning.E
import QuickSpec.Pruning.Simple
import QuickSpec.Rules
import QuickSpec.Signature
import QuickSpec.Term
import QuickSpec.Test
import QuickSpec.TestSet
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.PredicatesInterface
import QuickSpec.NamesFor
import QuickSpec.Resolve
