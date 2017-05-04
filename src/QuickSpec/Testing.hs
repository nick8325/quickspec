-- A type of test case generators.
{-# LANGUAGE MultiParamTypeClasses #-}
module QuickSpec.Testing where

import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Type

data Tester testcase prop =
  Tester {
    test :: prop -> Maybe (testcase, Tester testcase prop) }

makeTester ::
  (tester -> prop -> Maybe (testcase, tester)) ->
  tester -> Tester testcase prop
makeTester tst state =
  Tester {
    test = \prop ->
      case tst state prop of
        Nothing -> Nothing
        Just (testcase, state') ->
          Just (testcase, makeTester tst state') }

-- Miscellaneous stuff which is generally useful for testing.
class Valued f a where
  value :: a -> Value f

type TestCase f = Var -> Value f
