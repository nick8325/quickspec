import Data.Proxy
import QuickSpec.Haskell
import QuickSpec.Type

constants :: [Constant]
constants = [
  constant "+" ((+) :: Int -> Int -> Int),
  constant "*" ((*) :: Int -> Int -> Int),
  constant "0" (0 :: Int),
  constant "1" (1 :: Int)]

main = do
  quickSpec defaultConfig constants
    (typeRep (Proxy :: Proxy Int))
    [typeRep (Proxy :: Proxy Int), typeRep (Proxy :: Proxy (Int -> Int))]
