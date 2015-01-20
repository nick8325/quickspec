module QuickSpec.Pruning.Simple where

import QuickSpec.Base
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Utils
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Ord
import Data.Maybe
import Data.Rewriting.Rule
import qualified QuickSpec.Pruning.Index as Index
import QuickSpec.Pruning.Index (Index)
import QuickSpec.Pruning.Rewrite

newtype SimplePruner = S (Index (RuleOf PruningTerm))

instance Pruner SimplePruner where
  emptyPruner _ = S Index.empty
  untypedAxiom  = simpleUnify
  untypedRep    = simpleRep
  pruningReport = simpleReport

modifyS f = modify (\(S x) -> S (f x))

simpleUnify :: Monad m => PropOf PruningTerm -> StateT SimplePruner m ()
simpleUnify prop@([] :=>: t :=: u) = modifyS (Index.insert (Rule t u) . Index.insert (Rule u t))
simpleUnify _ = return ()

simpleRep :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT SimplePruner m (Maybe PruningTerm)
simpleRep axioms t = do
  S idx <- get
  let u = normaliseWith (usortBy (comparing measure) . anywhere (rewrite idx)) t
  if t == u then return Nothing else return (Just u)
  where
    rewrite idx t = do
      Rule _ u <- Index.lookup t idx
      guard (measure u < measure t)
      return u

simpleReport :: SimplePruner -> String
simpleReport (S eqs) = show (length (Index.elems eqs)) ++ " pruning equations.\n"
