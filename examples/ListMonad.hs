import Control.Monad
import QuickSpec

main =
  quickSpec signature {
    constants = [
      constant "return" (return :: A -> [A]),
      constant ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B]),
      constant "++" ((++) :: [A] -> [A] -> [A]),
      constant ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C]) ]}
