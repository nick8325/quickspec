-- | The main QuickSpec module.
module QuickSpec(
  quickSpec,
  quickSpecWithBackground,
  Signature(..),
  signature,
  constant,
  predicate,
  NamesFor(..),
  baseType,
  baseTypeNames,
  makeInstance,
  inst,
  observe,
  A, B, C, D, E) where

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
import QuickSpec.Instance
