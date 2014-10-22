-- A simple booleans example.

import Test.QuickSpec hiding (bools)

bools = [
  ["x", "y", "z"] `vars` (undefined :: Bool),

  "||"    `fun2` (||),
  "&&"    `fun2` (&&),
  "not"   `fun1` not,
  "True"  `fun0` True,
  "False" `fun0` False]

main = quickSpec bools
