import QuickSpec

sig =
  signature {
    maxTermSize = Just 7,
    predicates = [predicate "||" (||), predicate "&&" (&&), predicate "not" not],
    constants = [
       constant "True" True,
       constant "False" False
       ]}

main = quickSpec sig
