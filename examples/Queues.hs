{-# LANGUAGE TypeOperators, GeneralizedNewtypeDeriving, TypeApplications #-}

import QuickSpec
import Test.QuickCheck
import Prelude hiding (fst)

newtype Queue a = Queue [a] deriving (Eq, Ord, Arbitrary, CoArbitrary)
nil = Queue []
enq x (Queue ys) = Queue (ys ++ [x])
deq (Queue (x:xs)) = Queue xs
fst (Queue (x:xs)) = x

main = quickSpec [
  background [
    con "." ((.) @(Queue A) @(Queue A) @(Queue A)),
    con "id" (id @(Queue A)) ],

  inst (Sub Dict :: Ord A :- Ord (Queue A)),
  inst (Sub Dict :: Arbitrary A :- Arbitrary (Queue A)),
  inst (Sub Dict :: CoArbitrary A :- CoArbitrary (Queue A)),
  "enq" `con` (enq :: A -> Queue A -> Queue A),
  "deq" `con` (deq :: Queue A -> Queue A),
  "fst" `con` (fst :: Queue A -> A),
  "nil" `con` (nil :: Queue A)
  ]
