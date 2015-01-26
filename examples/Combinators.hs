import QuickSpec

main =
  quickSpec signature {
    constants = [
      constant "$" (($) :: (A -> B) -> (A -> B)),
      constant "s" ((\x y z -> x z (y z)) :: (A -> B -> C) -> (A -> B) -> A -> C) ]}
