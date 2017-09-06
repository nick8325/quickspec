-- | The main QuickSpec module.
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
  makeInstance,
  inst, inst2, inst3, inst4, inst5,
  observe) where

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
