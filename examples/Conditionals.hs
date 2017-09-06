{-# LANGUAGE TypeApplications #-}
-- A test for conditions.
-- Many laws for zip only hold when the arguments have the same
-- length.
import QuickSpec

eqLen :: [a] -> [b] -> Bool
eqLen xs ys = length xs == length ys

main = quickSpec [
  withMaxTermSize 8,
  withPruningDepth 10,
  con "++" ((++) @ Int),
  con "zip" (zip @ Int @ Int),
  predicate "eqLen" (eqLen @ Int @ Int) ]
