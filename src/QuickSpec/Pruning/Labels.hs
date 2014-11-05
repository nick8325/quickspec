-- Labels for supporting orphan murder.
module QuickSpec.Pruning.Labels where

import qualified Data.Set
import Data.Set(Set)

data Labels =
  Labels {
    labels    :: Set Label,
    nextLabel :: Int }

newtype Label = Label Int deriving (Eq, Ord, Num, Show)
data Labelled a = Labelled { labelOf :: Label, peel :: a } deriving (Show, Functor)
instance Eq a => Eq (Labelled a) where x == y = peel x == peel y
instance Ord a => Ord (Labelled a) where compare = comparing peel
instance Symbolic a => Symbolic (Labelled a) where
  type ConstantOf (Labelled a) = ConstantOf a
  type VariableOf (Labelled a) = VariableOf a
  termsDL = termsDL . peel
  substf sub (Labelled l x) = Labelled l (substf sub x)
instance Pretty a => Pretty (Labelled a) where pretty = pretty . peel

newLabel :: Monad m => StateT Completion m Label
newLabel = do
  Completion { nextLabel = n, labels = labels } <- get
  modify (\s -> s { nextLabel = n+1, labels = Set.insert n labels })
  return n

deleteLabel :: Monad m => Label -> StateT Completion m ()
deleteLabel l = modify (\s -> s { labels = Set.delete l (labels s) })

noLabel :: Label
noLabel = 0

unlabelled :: a -> Labelled a
unlabelled = Labelled noLabel

moveLabel :: Functor f => Labelled (f a) -> f (Labelled a)
moveLabel (Labelled l x) = fmap (Labelled l) x
