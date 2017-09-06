-- Just for testing polymorphic generalisation

import QuickSpec
import Data.Monoid

main = do
  thy <-
    quickSpec signature {
      constants = [
        constant "," ((,) :: A -> B -> (A, B)),
        constant "fst" (fst :: (A, B) -> A),
        constant "snd" (snd :: (A, B) -> B) ] }
  quickSpec $ thy `mappend` signature {
    constants = [constant "pair" (True, 'a')] }
