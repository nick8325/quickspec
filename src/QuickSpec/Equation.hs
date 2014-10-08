module QuickSpec.Equation where

import QuickSpec.Base
import QuickSpec.Term

data Equation = (:=:) { lhs, rhs :: Term }

instance Pretty Equation where
  pretty (t :=: u) =
    pretty t <+> text "=" <+> pretty u
