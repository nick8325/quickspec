import QuickSpec
import Signature

bools = [
  vars ["x", "y", "z"] True,
  fun2 "||" (||),
  fun2 "&&" (&&),
  fun1 "not" not, 
  fun0 "True" True,
  fun0 "False" False]

main = quickSpec bools
  -- r <- fmap toList (generate bools 3)
  -- forM_ r $ \(Some (C t)) ->
  --   mapM_ print (classes t)
