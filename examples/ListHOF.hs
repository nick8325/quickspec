import QuickSpec

sig =
  [ con "map"  (map   :: (A -> B) -> [A] -> [B])
  , con "fold" (foldr :: (A -> B -> B) -> B -> [A] -> B)
  , con "."    ((.)   :: (B -> C) -> (A -> B) -> (A -> C))
  , con "[]"   ([]    :: [A])
  , con ":"    ((:)   :: A -> [A] -> [A])
  ]

main = quickSpec sig
