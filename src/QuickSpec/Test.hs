-- The interface to testing in QuickSpec.

{-# LANGUAGE TypeFamilies #-}
module QuickSpec.Test where

data Result set = Equal (TesterTerm term) | Distinct set

class Tester set where
  type TesterTerm set
  test :: TesterTerm set -> set -> Result set
