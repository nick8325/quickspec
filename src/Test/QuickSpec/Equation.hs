module Test.QuickSpec.Equation where

import Test.QuickSpec.Base
import Test.QuickSpec.Term

data Equation = (:=:) { lhs, rhs :: Term }

instance Pretty Equation where
  pretty (t :=: u) =
    pretty t <+> text "=" <+> pretty u
