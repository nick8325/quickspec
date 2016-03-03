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
      constant "sort" (typeclass sort :: Dict (Ord A) -> [A] -> [A]),
      constant "concat" (concat :: [[A]] -> [A]) ]}

typeclass :: (c => a) -> Dict c -> a
typeclass x Dict = x

main = quickSpec sig
