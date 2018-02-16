import QuickSpec

main = quickSpec [
  predicate "not" not,
  con "True" True,
  con "False" False,
  con "||" (||),
  con "&&" (&&) ]
