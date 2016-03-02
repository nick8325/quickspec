import QuickSpec

sig =
  signature {
    maxTermSize = Just 7,
    constants = [
       constant "True" True,
       constant "False" False,
       constant "||" (||),
       constant "&&" (&&),
       constant "not" not ]}

main = quickSpec sig
