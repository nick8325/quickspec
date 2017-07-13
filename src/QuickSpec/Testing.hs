-- A type of test case generators.
{-# LANGUAGE MultiParamTypeClasses #-}
module QuickSpec.Testing where

import QuickSpec.Prop

data Tester testcase term =
  Tester {
    test :: Prop term -> Maybe (testcase, Tester testcase term) }

makeTester :: (Prop term -> Maybe testcase) -> Tester testcase term
makeTester tst = res
  where
    res =
      Tester {
        test = \prop ->
          case tst prop of
            Nothing -> Nothing
            Just testcase -> Just (testcase, res) }
