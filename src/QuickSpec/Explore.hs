{-# LANGUAGE FlexibleContexts #-}
module QuickSpec.Explore where

import QuickSpec.Explore.Schemas
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import Control.Monad.IO.Class
import Data.Maybe

baseTerms :: (Ord f, Typeable f, Ord a) => (Term f -> a) -> [f] -> [Type] -> [Term f]
baseTerms measure funs tys =
  sortBy' measure $
    [App f [] | f <- funs] ++
    [Var (V ty 0) | ty <- tys]

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
  (Ord measure, Ord fun, Typeable fun, Sized fun, Typed fun, Ord result, Apply (Term fun), PrettyTerm fun,
   MonadIO m, MonadPruner (Term fun) m, MonadTester testcase (Term fun) m) =>
  (Term fun -> measure) ->
  (Term fun -> testcase -> result) ->
  Int -> [fun] -> [Type] -> m ()
quickSpec measure eval maxSize funs tys = do
  let state0 = initialState (\t -> size t <= 5) eval

  loop state0 maxSize [[]] [] (baseTerms measure funs tys)
  where
    loop _ 1 _ _ [] = return ()
    loop state n tss ts [] =
      loop state (n-1) uss [] (moreTerms measure uss)
      where
        uss = tss ++ [ts]
    loop state n tss us (t:ts) = do
      ((state', terms), props) <- watchPruner (explore t state)
      mapM_ (liftIO . prettyPrint) props
      loop state' n tss (maybeToList terms ++ us) ts
