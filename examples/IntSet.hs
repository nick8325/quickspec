-- Laws about Data.IntSet.
-- Illustrates user-defined data types.
import QuickSpec
import qualified Data.IntSet as IntSet
import Data.IntSet(IntSet)

main = quickSpec [
  baseType (Proxy :: Proxy IntSet),

  series [sig1, sig2, sig3]]
  where
    sig1 = [
      con "union" IntSet.union,
      con "intersection" IntSet.intersection,
      con "empty" IntSet.empty ]
    
    sig2 = [
      con "insert" IntSet.insert,
      con "delete" IntSet.delete ]

    sig3 = [
      con "False" False,
      predicate "member" IntSet.member ]
