import QuickSpec

sig =
  signature {
    constants = [
       constant "const" (const :: A -> B -> A),
       constant "asTypeOf" (asTypeOf :: A -> A -> A) ] }

main = quickSpec sig
