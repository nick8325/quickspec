{-# LANGUAGE TypeApplication #-}
import QuickSpec

eqLen :: [A] -> [B] -> Bool
eqLen xs ys = length xs == length ys

main = quickSpec [
  withMaxTermSize 8,
  con "++" ((++) @ A),
  con "zip" (zip @ A @ B),
  predicate "eqLen" (eqLen @ Int @ Int) ]
