-- | The main QuickSpec module.
--
-- Look at the introduction (<https://github.com/nick8325/quickspec/blob/master/README.asciidoc>),
-- read the examples (<http://github.com/nick8325/quickspec/tree/master/examples>),
-- or read the paper (<http://www.cse.chalmers.se/~nicsma/quickspec.pdf>)
-- before venturing in here.

module Test.QuickSpec
  (-- * Running QuickSpec
   quickSpec,
   sampleTerms,

   -- * The Signature class
   Sig,
   Signature(..),
   -- * Adding functions to a signature
   --
   -- | You can add @f@ to the signature by using @\"f\" \`funN\` f@,
   -- where @N@ is the arity of the function. For example,
   --
   -- > "&&" `fun2` (&&)
   --
   -- will add the binary function @(`&&`)@ to the signature.
   --
   -- If f is polymorphic, you must explicitly give it a monomorphic type.
   -- This module exports types `A`, `B` and `C` for that purpose.
   --
   -- For example:
   --
   -- > "++" `fun2` ((++) :: [A] -> [A] -> [A])
   --
   -- The result type of the function must be a member of `Ord`.
   -- If it isn't, use the `blindN` family of functions (below) instead.
   -- If you want to get equations over a type that isn't in `Ord`,
   -- you must use the `observerN` family of functions (below)
   -- to define an observation function for that type.
   con, fun0, fun1, fun2, fun3, fun4, fun5,
   -- * Adding functions whose results are not in `Ord`
   --
   -- | These functions work the same as `funN` (above),
   --   but don't use `Ord` to compare the results of the functions.
   --   Instead you can use the `observerN` family of functions (below)
   --   to define an observation function.
   blind0, blind1, blind2, blind3, blind4, blind5,
   -- * Adding variables to a signature
   vars,
   gvars,
   -- * Observational equality
   --
   -- | Use this to define comparison operators for types that have
   --   no `Ord` instance.
   --
   -- For example, suppose we have a type @Regex@ of regular expressions,
   -- and a matching function @match :: String -> Regex -> Bool@.
   -- We want our equations to talk about semantic equality of regular
   -- expressions, but we probably won't have an `Ord` instance that does that.
   -- Instead, we can use @blindN@ to add the regular expression operators
   -- to the signature, and then write
   --
   -- > observer2 match
   --
   -- (the @2@ is because @match@ has arity two).
   -- Then, when QuickSpec wants to compare two @Regex@es, @r1@ and @r2@, it will generate a random
   -- `String` @xs@, and compare @match xs r1@ with @match xs r2@.
   --
   -- Thus you can use `observerN` to get laws about things that can't
   -- be directly compared for equality but can be tested.
   observer1, observer2, observer3, observer4,
   -- * Modifying a signature
   background,
   withDepth,
   withSize,
   withTests,
   withQuickCheckSize,
   without,

   -- * The standard QuickSpec prelude, to include in your own signatures
   A, B, C,
   Two,
   prelude,
   bools,
   arith,
   lists,
   funs)

where

import Test.QuickSpec.Main
import Test.QuickSpec.Signature
import Test.QuickSpec.Prelude
