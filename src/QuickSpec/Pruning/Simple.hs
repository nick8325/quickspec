module QuickSpec.Pruning.Simple where

import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Utils
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Ord
import Data.Maybe
import Twee.Base
import Twee.Index(Index)
import qualified Twee.Index as Index
import Twee.Rule hiding ((:=:))
import qualified Twee.Rule as Rule
import qualified Data.Set as Set

newtype SimplePruner = S (Index (Rule PruningConstant))

instance Pruner SimplePruner where
  emptyPruner _  = S Index.Nil
  untypedAxiom _ = simpleUnify
  untypedRep     = simpleRep
  pruningReport  = simpleReport

modifyS f = modify (\(S x) -> S (f x))

simpleUnify :: PruningProp -> StateT SimplePruner IO ()
simpleUnify prop@([] :=>: t :=: u) = do
  let rules = orient (t Rule.:=: u)
  modifyS (\s -> foldr Index.insert s rules)
simpleUnify _ = return ()

simpleRep :: [PropOf PruningTerm] -> PruningTerm -> StateT SimplePruner IO (Maybe PruningTerm)
simpleRep axioms t = do
  S idx <- get
  let ts = normalForms (rewrite "simple-pruner" reduces (Index.freeze idx)) [t]
  if Set.null ts then return Nothing else return (Just (minimumBy lessEq (Set.toList ts)))

simpleReport :: SimplePruner -> String
simpleReport (S eqs) = show (length (Index.elems eqs)) ++ " pruning equations."
