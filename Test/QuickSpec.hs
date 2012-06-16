module Test.QuickSpec
  (quickSpec,
   sampleTerms,

   Signature(..),
   Sig,
   blind0, blind1, blind2, blind3, blind4,
   con, fun0, fun1, fun2, fun3, fun4,
   vars,
   observer0, observer1, observer2, observer3, observer4,
   silence,
   withDepth,

   A,
   prelude,
   bools,
   arith,
   lists,
   funs)

where

import Test.QuickSpec.Main
import Test.QuickSpec.Signature
import Test.QuickSpec.Prelude
