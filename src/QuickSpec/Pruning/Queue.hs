-- A priority queue, with orphan murder.
{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, DeriveFunctor #-}
module QuickSpec.Pruning.Queue where

import QuickSpec.Base
import Data.Ord
import qualified Data.Heap as Heap
import Data.Heap(Heap)
import qualified Data.Set as Set
import Data.Set(Set)

data Queue a =
  Queue {
    queue     :: Heap (Labelled (Subqueue a)),
    labels    :: Set Label,
    nextLabel :: Label }
  deriving Show

newtype Subqueue a =
  Subqueue { unSubqueue :: Heap (Labelled a) }
  deriving Show

instance Eq a => Eq (Subqueue a) where
  Subqueue x == Subqueue y = getMin x == getMin y
instance Ord a => Ord (Subqueue a) where
  compare = comparing (\(Subqueue x) -> getMin x)

getMin :: Heap a -> Maybe a
getMin h
  | Heap.null h = Nothing
  | otherwise = Just (Heap.minimum h)

empty :: Queue q
empty = Queue Heap.empty (Set.singleton noLabel) (noLabel+1)

enqueue :: Ord a => Label -> [Labelled a] -> Queue a -> Queue a
enqueue l [] q = q
enqueue l xs q = q { queue = Heap.insert q' (queue q) }
  where
    q' = Labelled l (Subqueue (Heap.fromList xs))

dequeue :: Ord a => Queue a -> Maybe (Label, Label, a, Queue a)
dequeue q@Queue{labels = ls, queue = q0} =
  fmap (\(l1, l2, x, q1) -> (l1, l2, x, q { queue = q1 })) (dequeue1 q0)
  where
    dequeue1 q = do
      (Labelled l (Subqueue sq), q) <- Heap.viewMin q
      case viewMin sq of
        Nothing -> dequeue1 q
        Just (Labelled l' x, sq) ->
          return (l, l', x, Heap.insert (Labelled l (Subqueue sq)) q)

    viewMin ::
      Ord a =>
      Heap (Labelled a) ->
      Maybe (Labelled a, Heap (Labelled a))
    viewMin q = do
      x@(Labelled l _, q) <- Heap.viewMin q
      if l `Set.member` ls then return x else viewMin q

newtype Label = Label Int deriving (Eq, Ord, Num, Show)

noLabel :: Label
noLabel = 0

newLabel :: Queue a -> (Label, Queue a)
newLabel q@Queue{nextLabel = n, labels = ls} =
  (n, q { nextLabel = n+1, labels = Set.insert n ls } )

deleteLabel :: Label -> Queue a -> Queue a
deleteLabel l q@Queue{labels = ls} = q { labels = Set.delete l ls }

data Labelled a = Labelled { labelOf :: Label, peel :: a } deriving (Show, Functor)

instance Eq a => Eq (Labelled a) where x == y = peel x == peel y
instance Ord a => Ord (Labelled a) where compare = comparing peel
instance Symbolic a => Symbolic (Labelled a) where
  type ConstantOf (Labelled a) = ConstantOf a
  type VariableOf (Labelled a) = VariableOf a
  termsDL = termsDL . peel
  substf sub (Labelled l x) = Labelled l (substf sub x)
instance Pretty a => Pretty (Labelled a) where pretty = pretty . peel

moveLabel :: Functor f => Labelled (f a) -> f (Labelled a)
moveLabel (Labelled l x) = fmap (Labelled l) x

unlabelled :: a -> Labelled a
unlabelled = Labelled noLabel

