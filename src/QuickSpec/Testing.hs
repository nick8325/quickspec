-- A type of test case generators.
{-# LANGUAGE MultiParamTypeClasses #-}
module QuickSpec.Testing where

data Tester testcase prop =
  Tester {
    test :: prop -> Maybe (testcase, Tester testcase prop) }

makeTester :: (prop -> Maybe testcase) -> Tester testcase prop
makeTester tst = res
  where
    res =
      Tester {
        test = \prop ->
          case tst prop of
            Nothing -> Nothing
            Just testcase -> Just (testcase, res) }
