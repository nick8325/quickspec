-- Testing functions on booleans. "not x" is used as a condition.
import QuickSpec

sig =
  signature {
    predicates = [predicate "not" not],
    constants = [
       constant "True" True,
       constant "False" False,
       constant "||" (||),
       constant "&&" (&&)
       ]}

main = quickSpec sig
