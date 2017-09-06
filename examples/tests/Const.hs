import QuickSpec

main = quickSpec [
  con "const" (const :: A -> B -> A),
  con "asTypeOf" (asTypeOf :: A -> A -> A) ]
