{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds, FlexibleContexts #-}
import QuickSpec
import Data.List

sig =
  signature {
    maxTermSize = Just 9,
    constants = [
      constant "reverse" (reverse :: [A] -> [A]),
      constant "++" ((++) :: [A] -> [A] -> [A]),
      constant "[]" ([] :: [A]),
      constant "map" (map :: (A -> B) -> [A] -> [B]),
      constant "length" (length :: [A] -> Int),
      constant "concat" (concat :: [[A]] -> [A]) ]}

main = quickSpec sig
