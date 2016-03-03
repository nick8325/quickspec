import QuickSpec

main =
  quickSpec signature {
    constants = [
      constant "s" ((\x y z -> x z (y z)) :: (A -> B -> C) -> (A -> B) -> A -> C),
      constant "k" (const :: A -> B -> A),
      constant "i" (id :: A -> A) ]}
