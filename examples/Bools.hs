import QuickSpec

sig =
  signature {
    maxTermSize = Just 7,
    predicates = [predicate "not" not],
    constants = [
       constant "True" True,
       constant "False" False,
       constant "||" (||),
       constant "&&" (&&)
       ]}

main = quickSpec sig
