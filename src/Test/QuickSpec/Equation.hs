module Test.QuickSpec.Equation where

import Test.QuickSpec.Term

data Equation = Term :=: Term

lhs, rhs :: Typed Equation -> Typed Term
lhs Typed { untyped = l :=: _ } = Typed { untyped = l }
rhs Typed { untyped = _ :=: r } = Typed { untyped = r }
