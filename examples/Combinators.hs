import QuickSpec

main = quickSpec [
  con "s" ((\x y z -> x z (y z)) :: (A -> B -> C) -> (A -> B) -> A -> C),
  con "k" (const :: A -> B -> A),
  con "i" (id :: A -> A) ]
