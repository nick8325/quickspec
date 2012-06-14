module QuickSpec where

import Generate
import NaiveEquationalReasoning hiding (universe, maxDepth)
import Typed
import TypeMap(TypeMap)
import qualified TypeMap
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
import System.Random

data Equation a = Term a :=: Term a

compareSomeEquations (Some eq1) (Some eq2) =
  compareEquations eq1 eq2
compareEquations (t :=: u) (v :=: w) =
  compareTerms t v `orElse` compareTerms u w

undefinedSig :: Sig -> Sig
undefinedSig sig =
  mconcat
    [ constantValue "undefined" (Undefined `asTypeOf` Value (witness x))
    | Some x <- TypeMap.toList (witnesses sig) ]

untypedClasses :: TypeMap (C TestResults Term) -> [Some (C [] Term)]
untypedClasses = concatMap (disperse . mapSome (C . map C . classes . unC)) . TypeMap.toList

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

runTool :: Signature a => (Sig -> IO ()) -> a -> IO ()
runTool tool sig_ = do
  putStrLn "== API =="
  print (signature sig_)
  
  let sig = signature sig_ `mappend` undefinedSig (signature sig_)
  tool sig

quickSpec :: Signature a => a -> IO ()
quickSpec = runTool $ \sig -> do
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

  putStrLn ""

sampleList :: StdGen -> Int -> [a] -> [a]
sampleList g n xs | n >= length xs = xs
                  | otherwise = aux g n (length xs) xs
  where
    aux g 0 _ _ = []
    aux g _ _ [] = error "QuickSpec.sampleList: bug in sampling"
    aux g size len (x:xs)
      | i <= size = x:aux g' (size-1) (len-1) xs
      | otherwise = aux g' size (len-1) xs
      where (i, g') = randomR (1, len) g

sampleTerms :: Signature a => a -> IO ()
sampleTerms = runTool $ \sig -> do
  putStrLn "== Testing =="
  r <- generate sig
  let univ = universe r
      numTerms = 100

  printf "\n== Here are %d terms out of a total of %d ==\n" numTerms (length univ)
  g <- newStdGen
  forM_ (zip [1..] (sampleList g numTerms univ)) $ \(i, Some t) ->
    printf "%d: %s\n" i (show t)

  putStrLn ""
