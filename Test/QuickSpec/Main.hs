{-# LANGUAGE TypeOperators #-}
module Test.QuickSpec.Main where

import Test.QuickSpec.Generate
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning hiding (universe, maxDepth)
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.TypeMap(TypeMap)
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import Test.QuickSpec.Signature
import Test.QuickSpec.Term
import Control.Monad
import Text.Printf
import Data.Monoid
import Test.QuickSpec.TestTree(TestResults, classes, reps)
import Data.List
import System.Random

data Equation = Term :=: Term deriving (Eq, Ord)

instance Show Equation where
  show (t :=: u) = show t ++ " == " ++ show u

undefinedsSig :: Sig -> Sig
undefinedsSig sig =
  mconcat
    [ undefinedSig "undefined" (undefined `asTypeOf` witness x)
    | Some x <- map (findWitness sig) (inhabitedTypes sig) ]

untypedClasses :: TypeMap (TestResults `O` Expr) -> [[Typed Term]]
untypedClasses = concatMap (some (map (map (tag term)) . classes . unO)) . TypeMap.toList

universe :: [[Typed Term]] -> [Typed Term]
universe css = filter (not . isUndefined . erase) (concat css)

equations :: [[Typed Term]] -> [Equation]
equations = sort . concatMap (toEquations . map erase)
  where toEquations (x:xs) = [y :=: x | y <- xs]

prune :: Int -> [Typed Term] -> [Equation] -> [Equation]
prune d univ eqs = evalEQ (initial d univ) (filterM (fmap not . provable) eqs)
  where provable (t :=: u) = t =:= u

runTool :: Signature a => (Sig -> IO ()) -> a -> IO ()
runTool tool sig_ = do
  putStrLn "== API =="
  print (signature sig_)
  let sig = signature sig_ `mappend` undefinedsSig (signature sig_)

  tool sig

quickSpec :: Signature a => a -> IO ()
quickSpec = runTool $ \sig -> do
  putStrLn "== Testing =="
  r <- generate sig
  let clss = untypedClasses r
      eqs = equations clss
      univ = universe clss
  printf "%d raw equations; %d terms in universe.\n\n"
    (length eqs)
    (length univ)

  putStrLn "== Equations =="
  let pruned = filter (not . all silent . eqnFuns)
                 (prune (maxDepth sig) univ eqs)
      eqnFuns (t :=: u) = funs t ++ funs u
  forM_ (zip [1 :: Int ..] pruned) $ \(i, eq) ->
    printf "%d: %s\n" i (show eq)

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
  r <- generate (updateDepth (maxDepth sig - 1) sig)
  let univ = concatMap (some2 (map term)) . TypeMap.toList . terms sig .
             TypeMap.mapValues2 reps $ r
  printf "Universe contains %d terms.\n\n" (length univ)

  let numTerms = 100

  printf "== Here are %d terms out of a total of %d ==\n" numTerms (length univ)
  g <- newStdGen
  forM_ (zip [1 :: Int ..] (sampleList g numTerms univ)) $ \(i, t) ->
    printf "%d: %s\n" i (show t)

  putStrLn ""
