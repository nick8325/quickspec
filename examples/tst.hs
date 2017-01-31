import QuickSpec
import Test.QuickCheck
import Data.Dynamic

sig = signature {
  predicates = [predicateGen "gt0" ((>0) :: Int -> Bool) (sequence [toDyn <$> (+1) <$> abs <$> (arbitrary :: Gen Int)])]
  }

main = quickSpec sig
