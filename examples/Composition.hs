-- Function composition.
import QuickSpec

main = quickSpec [
  con "id" (id :: A -> A),
  con "." ((.) :: (B -> C) -> (A -> B) -> A -> C) ]
