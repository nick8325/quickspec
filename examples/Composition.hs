import QuickSpec

main =
  quickSpec signature {
    constants = [
      constant "id" (id :: A -> A),
      constant "." ((.) :: (B -> C) -> (A -> B) -> A -> C) ]}
