-- | Main QuickSpec module.  Exports basic functionality.
--
-- This is typically the only module you need when using QuickSpec.
module QuickSpec(
  module QuickSpec.PredicatesInterface,
  module QuickSpec.Eval,
  module QuickSpec.Parse,
  module QuickSpec.Prop,
  module QuickSpec.Pruning,
  module QuickSpec.Pruning.E,
  module QuickSpec.Pruning.Simple,
  module QuickSpec.Rules,
  module QuickSpec.Signature,
  module QuickSpec.Instance,
  module QuickSpec.Term,
  module QuickSpec.Test,
  module QuickSpec.TestSet,
  module QuickSpec.Type,
  module QuickSpec.Utils,
  module Data.Constraint) where

import QuickSpec.Eval hiding (terms)
import QuickSpec.Parse
import QuickSpec.Prop
import QuickSpec.Pruning hiding (createRules, instances)
import QuickSpec.Pruning.E
import QuickSpec.Pruning.Simple hiding (S)
import QuickSpec.Rules
import QuickSpec.Signature
import QuickSpec.Term
import QuickSpec.Test
import QuickSpec.TestSet
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.PredicatesInterface
import QuickSpec.Instance
import Data.Constraint
