{-# LANGUAGE GeneralizedNewtypeDeriving, TypeApplications, TypeOperators #-}
import QuickSpec
import qualified Data.Map as Map
import Test.QuickCheck
import Data.Map(Map)

newtype Key = Key Int deriving (Eq, Ord, Arbitrary)
newtype Value = Value Int deriving (Eq, Ord, Arbitrary)

main = quickSpec [
  withMaxTermSize 8,
  monoTypeWithVars ["k"] (Proxy :: Proxy Key),
  monoTypeWithVars ["v"] (Proxy :: Proxy Value),
  monoTypeWithVars ["m"] (Proxy :: Proxy (Map Key Value)),

  background [
    predicate "/=" ((/=) :: Key -> Key -> Bool),
    con "Nothing" (Nothing :: Maybe A),
    con "Just" (Just :: A -> Maybe A)],

  series [sig1, sig2, sig3]]
  where
    sig1 = [
      con "empty" (Map.empty :: Map Key Value),
      con "lookup" (Map.lookup :: Key -> Map Key Value -> Maybe Value)]
    sig2 = [
      con "insert" (Map.insert :: Key -> Value -> Map Key Value -> Map Key Value)]
    sig3 = [
      con "delete" (Map.delete :: Key -> Map Key Value -> Map Key Value)]
