module Test.QuickSpec.Equation where

import Test.QuickSpec.Base
import Test.QuickSpec.Term

data Equation = Term :=: Term

equation :: Typed Term -> Typed Term -> Typed Equation
equation t u
  | typ t == typ u && context t == context u =
    Typed (untyped t :=: untyped u) (context t) (typ t)

lhs, rhs :: Typed Equation -> Typed Term
lhs t@Typed { untyped = l :=: _ } = t { untyped = l }
rhs t@Typed { untyped = _ :=: r } = t { untyped = r }

instance Pretty Equation where
  pretty (t :=: u) =
    pretty t <+> text "=" <+> pretty u
