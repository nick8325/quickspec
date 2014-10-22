import QuickSpec

sig =
  signature {
    constants = [
       constant "True" True,
       constant "False" False,
       constant "||" (||),
       constant "&&" (&&),
       constant "not" not ]}

main = quickSpec sig
