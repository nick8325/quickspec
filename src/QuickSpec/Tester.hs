-- A type of testers.
module QuickSpec.Tester where

data Tester term =
  Tester {
    test :: term -> Result term }

data Result term = EqualTo term | Distinct (Tester term)

makeTester ::
  (term -> tester -> Either term tester) ->
  tester -> Tester term
makeTester test state =
  Tester {
    test = \t ->
      case test t state of
        Left u -> EqualTo u
        Right state' -> Distinct (makeTester test state') }
