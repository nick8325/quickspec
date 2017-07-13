{-# LANGUAGE FlexibleContexts #-}
module QuickSpec.Explore where

import QuickSpec.Explore.Terms
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils

baseTerms :: (Ord f, Typeable f, Ord a) => (Term f -> a) -> [f] -> [Type] -> [Term f]
baseTerms measure funs tys =
  sortBy' measure $
    map build $
    [con (fun f) | f <- funs] ++
    zipWith (\ty n -> var (V ty n)) (concatMap (replicate 3) tys) [0..]

moreTerms :: (Ord a, Apply (Term f)) => (Term f -> a) -> [[Term f]] -> [Term f]
moreTerms measure tss =
  sortBy' measure $
    [ v
    | i <- [0..n-1],
      t <- tss !! i,
      u <- tss !! (n-i),
      Just v <- [tryApply t u] ]
  where
    n = length tss

quickSpec :: (Ord a, Ord f, Typeable f, Ord result, Apply (Term f), PrettyTerm f) =>
  (Term f -> a) ->
  (Term f -> testcase -> result) ->
  Tester testcase (Term f) ->
  Pruner (Term f) ->
  Int -> [f] -> [Type] -> IO ()
quickSpec measure eval tester pruner size funs tys = do
  let state0 = initialState eval tester pruner

  loop state0 size [[]] [] (baseTerms measure funs tys)
  where
    loop state 1 _ _ [] = return ()
    loop state n tss ts [] =
      loop state (n-1) uss [] (moreTerms measure uss)
      where
        uss = tss ++ [ts]
    loop state n tss us (t:ts) = do
      let (state', mprop) = explore t state
      case mprop of
        Redundant ->
          loop state' n tss us ts
        Unique ->
          loop state' n tss (t:us) ts
        Discovered prop -> do
          prettyPrint prop
          loop state' n tss us ts
