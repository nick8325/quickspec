-- A type of test case generators.
module QuickSpec.Testing where

import QuickSpec.Prop

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
