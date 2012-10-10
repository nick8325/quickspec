-- | The main implementation of QuickSpec.

{-# LANGUAGE TypeOperators #-}
module Test.QuickSpec.Main where

import Test.QuickSpec.Generate
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning hiding (universe, maxDepth)
import Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import Test.QuickSpec.Signature hiding (vars)
import Test.QuickSpec.Term
import Control.Monad
import Text.Printf
import Data.Monoid
import Test.QuickSpec.TestTree(TestResults, classes, reps)
import Data.List
import System.Random
import Data.Monoid
import Data.Maybe
import Test.QuickSpec.Utils
import Test.QuickSpec.Equation

undefinedsSig :: Sig -> Sig
undefinedsSig sig =
  background
    [ undefinedSig "undefined" (undefined `asTypeOf` witness x)
    | Some x <- saturatedTypes sig ]

universe :: [[Tagged Term]] -> [Tagged Term]
universe css = filter (not . isUndefined . erase) (concat css)

prune :: Int -> [Tagged Term] -> [Term] -> [Equation] -> [Equation]
prune d univ reps eqs = evalEQ (initial d univ) (filterM (fmap not . provable) eqs)
  where
    provable (t :=: u) = do
      res <- t =?= u
      if res then return True else do
        state <- get
        -- Check that we won't unify two representatives---if we do
        -- the equation is false
        t =:= u
        reps' <- mapM rep reps
        if sort reps' == usort reps' then return False else do
          put state
          return True

defines :: Equation -> Maybe Symbol
defines (t :=: u) = do
  let isVar Var{} = True
      isVar _ = False

      acyclic t =
        all acyclic (args t) &&
        case functor t == functor u of
          True -> usort (map Var (vars t)) `isProperSubsetOf` args u
          False -> True
      xs `isProperSubsetOf` ys = xs `isSubsetOf` ys && sort xs /= sort ys
      xs `isSubsetOf` ys = sort xs `isSublistOf` sort ys
      [] `isSublistOf` _ = True
      (x:xs) `isSublistOf` [] = False
      (x:xs) `isSublistOf` (y:ys)
        | x == y = xs `isSublistOf` ys
        | otherwise = (x:xs) `isSublistOf` ys

  guard (all isVar (args u) && usort (args u) == args u &&
         acyclic t && vars t `isSubsetOf` vars u)

  return (functor u)

definitions :: [Equation] -> [Equation]
definitions es = [ e | e <- es, defines e /= Nothing ]

runTool :: Signature a => (Sig -> IO ()) -> a -> IO ()
runTool tool sig_ = do
  putStrLn "== API =="
  putStr (show (signature sig_))
  let sig = signature sig_ `mappend` undefinedsSig (signature sig_)

  tool sig

quickSpec :: Signature a => a -> IO ()
quickSpec = runTool $ \sig -> do
  putStrLn "== Testing =="
  r <- generate sig
  let clss = eraseClasses r
      reps = map (erase . head) clss
      eqs = equations clss
      univ = universe clss
  printf "%d raw equations; %d terms in universe.\n\n"
    (length eqs)
    (length univ)

  let pruned = filter (not . all silent . eqnFuns)
                 (prune (maxDepth sig) univ reps eqs)
      eqnFuns (t :=: u) = funs t ++ funs u
      isGround (t :=: u) = null (vars t) && null (vars u)
      (ground, nonground) = partition isGround pruned
  putStrLn "== Ground equations =="
  forM_ (zip [1 :: Int ..] ground) $ \(i, eq) ->
    printf "%3d: %s\n" i (showEquation sig eq)
  putStrLn ""

  putStrLn "== Non-ground equations =="
  forM_ (zip [length ground + 1 ..] nonground) $ \(i, eq) ->
    printf "%3d: %s\n" i (showEquation sig eq)
  putStrLn ""

sampleList :: StdGen -> Int -> [a] -> [a]
sampleList g n xs | n >= length xs = xs
                  | otherwise = aux g n (length xs) xs
  where
    aux g 0 _ _ = []
    aux g _ _ [] =
      error "Test.QuickSpec.Main.sampleList: bug in sampling"
    aux g size len (x:xs)
      | i <= size = x:aux g' (size-1) (len-1) xs
      | otherwise = aux g' size (len-1) xs
      where (i, g') = randomR (1, len) g

sampleTerms :: Signature a => a -> IO ()
sampleTerms = runTool $ \sig -> do
  putStrLn "== Testing =="
  r <- generate (updateDepth (maxDepth sig - 1) sig)
  let univ = sort . concatMap (some2 (map term)) . TypeMap.toList . terms sig .
             TypeMap.mapValues2 reps $ r
  printf "Universe contains %d terms.\n\n" (length univ)

  let numTerms = 100

  printf "== Here are %d terms out of a total of %d ==\n" numTerms (length univ)
  g <- newStdGen
  forM_ (zip [1 :: Int ..] (sampleList g numTerms univ)) $ \(i, t) ->
    printf "%d: %s\n" i (show (disambiguate sig (vars t) t))

  putStrLn ""
