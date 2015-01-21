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
import QuickSpec.Pruning.Constraints
import QuickSpec.Pruning.Equation

newtype SimplePruner = S (Index (Constrained (RuleOf PruningTerm)))

instance Pruner SimplePruner where
  emptyPruner _ = S Index.empty
  untypedAxiom  = simpleUnify
  untypedRep    = simpleRep
  pruningReport = simpleReport

modifyS f = modify (\(S x) -> S (f x))

simpleUnify :: PropOf PruningTerm -> StateT SimplePruner IO ()
simpleUnify prop@([] :=>: t :=: u) = do
  let rules = orient (t :==: u)
  modifyS (\s -> foldr Index.insert s rules)
simpleUnify _ = return ()

simpleRep :: [PropOf PruningTerm] -> PruningTerm -> StateT SimplePruner IO (Maybe PruningTerm)
simpleRep axioms t = do
  S idx <- get
  let u = normaliseWith (usortBy (comparing measure) . anywhere (rewrite idx)) t
  if t == u then return Nothing else return (Just u)
  where
    rewrite idx t = do
      Constrained ctx (Rule _ u) <- Index.lookup t idx
      guard (true (formula ctx))
      return u

simpleReport :: SimplePruner -> String
simpleReport (S eqs) = show (length (Index.elems eqs)) ++ " pruning equations.\n"
