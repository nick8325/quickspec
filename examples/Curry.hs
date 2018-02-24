import QuickSpec

main = quickSpec [
  con "curry" (curry :: ((A, B) -> C) -> A -> B -> C),
  con "fst" (fst :: (A, B) -> A),
  con "snd" (snd :: (A, B) -> B),
  con "id" (id :: A -> A),
  con "." ((.) :: (B -> C) -> (A -> B) -> A -> C),
  con "|" ((\f g x -> (f x, g x)) :: (A -> B) -> (A -> C) -> A -> (B, C))]
