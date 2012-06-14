{-# LANGUAGE DeriveDataTypeable #-}
module QuickSpec where

import Generate
import NaiveEquationalReasoning hiding (universe, maxDepth)
import Typed
import Signature
import Term
import Control.Monad
import Text.Printf
import Data.Monoid
import TestTree
import Data.Typeable
import Data.List
import Control.Applicative
import Utils

data Equation a = Term a :=: Term a deriving Typeable

compareSomeEquations (Some eq1) (Some eq2) =
  compareEquations eq1 eq2
compareEquations (t :=: u) (v :=: w) =
  compareTerms t v `orElse` compareTerms u w

undefinedSig :: Sig -> Sig
undefinedSig sig =
  mconcat
    [ constantValue "undefined" (witness Undefined x)
    | Some x <- Typed.toList (witnesses sig) ]
  where witness :: Value a -> K () a -> Value a
        witness x _ = x

untypedClasses :: TypeMap (C TestResults Term) -> [Some (C [] Term)]
untypedClasses = concatMap (disperse . mapSome (C . map C . classes . unC)) . toList

universe :: TypeMap (C TestResults Term) -> [Some Term]
universe = concatMap disperse . untypedClasses

equations :: TypeMap (C TestResults Term) -> [Some Equation]
equations = sortBy compareSomeEquations .
            concatMap (disperse . mapSome (C . toEquations . unC)) . untypedClasses
  where toEquations :: [Term a] -> [Equation a]
        toEquations (x:xs) = [y :=: x | y <- xs]

prune :: Int -> [Some Term] -> [Some Equation] -> [Some Equation]
prune d univ eqs = evalEQ (initial d univ) (filterM (fmap not . provable) eqs)
  where provable (Some (t :=: u)) = t =:= u

quickSpec :: Signature a => a -> IO ()
quickSpec sig_ = do
  putStrLn "== API =="
  print (signature sig_)
  
  let sig = signature sig_ `mappend` undefinedSig (signature sig_)
  
  putStrLn "== Testing =="
  r <- generate sig
  let eqs = equations r
      univ = universe r
  printf "%d raw equations; %d terms in universe.\n\n"
    (length eqs)
    (length univ)
  
  putStrLn "== Equations =="
  let pruned = filter (not . all silent . eqnFuns)
                 (prune (maxDepth sig) univ (equations r))
      eqnFuns (Some (t :=: u)) = funs t ++ funs u
  forM_ (zip [1..] pruned) $ \(i, Some (t :=: u)) ->
    printf "%d: %s == %s\n" i (show t) (show u)

