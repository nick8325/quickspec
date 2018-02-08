{-# LANGUAGE FlexibleContexts #-}
module QuickSpec.Explore where

import QuickSpec.Explore.Terms
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import Control.Monad.IO.Class

baseTerms :: (Ord f, Typeable f, Ord a) => (Term f -> a) -> [f] -> [Type] -> [Term f]
baseTerms measure funs tys =
  sortBy' measure $
    [App f [] | f <- funs] ++
    zipWith (\ty n -> Var (V ty n)) (concatMap (replicate 3) tys) [0..]

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

quickSpec ::
  (Ord measure, Ord fun, Typeable fun, Ord result, Apply (Term fun), PrettyTerm fun,
   MonadIO m, MonadPruner (Term fun) m, MonadTester testcase (Term fun) m) =>
  (Term fun -> measure) ->
  (Term fun -> testcase -> result) ->
  Int -> [fun] -> [Type] -> m ()
quickSpec measure eval size funs tys = do
  let state0 = initialState eval

  loop state0 size [[]] [] (baseTerms measure funs tys)
  where
    loop _ 1 _ _ [] = return ()
    loop state n tss ts [] =
      loop state (n-1) uss [] (moreTerms measure uss)
      where
        uss = tss ++ [ts]
    loop state n tss us (t:ts) = do
      (state', res) <- explore t state
      case res of
        Singleton ->
          loop state' n tss (t:us) ts
        Discovered prop -> do
          liftIO (prettyPrint prop)
          loop state' n tss us ts
        Knew _ ->
          loop state' n tss us ts
