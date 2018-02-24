-- Partial functions.
import QuickSpec

main = quickSpec [
  con "head" (head :: [A] -> A),
  con "tail" (tail :: [A] -> [A]),
  con ":" ((:) :: A -> [A] -> [A])]
