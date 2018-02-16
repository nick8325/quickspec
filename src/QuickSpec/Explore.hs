{-# LANGUAGE FlexibleContexts #-}
module QuickSpec.Explore where

import QuickSpec.Explore.Polymorphic
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.Prop
import QuickSpec.Terminal
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Debug.Trace

moreTerms :: (Ord a, Apply (Term f), Sized f) => Universe -> [f] -> (Term f -> a) -> [[Term f]] -> [Term f]
moreTerms univ funs measure tss =
  sortBy' measure $
    atomic ++
    [ unPoly v
    | i <- [0..n],
      t <- uss !! i,
      u <- uss !! (n-i),
      Just v <- [tryApply (poly t) (poly u)],
      and [ typ x `inUniverse` univ | x <- subterms (unPoly v) ] ]
  where
    n = length tss
    atomic =
      [App f [] | f <- funs, size f == n] ++
      [Var (V typeVar 0) | n == 1]
    uss = tss ++ [atomic]

quickSpec ::
  (Ord measure, Ord fun, Ord norm, Sized fun, Typed fun, Ord result, Apply (Term fun), PrettyTerm fun,
   MonadPruner (Term fun) norm m, MonadTester testcase (Term fun) m, MonadTerminal m) =>
  (Prop (Term fun) -> m ()) ->
  (Term fun -> measure) ->
  (Term fun -> testcase -> result) ->
  Int -> [fun] -> m ()
quickSpec present measure eval maxSize funs = do
  let
    univ = universe funs
    state0 = initialState univ (\t -> size t <= 5) eval

    loop m n _ _ _ | m > n = return ()
    loop m n tss ts [] = do
      loop (m+1) n uss [] (moreTerms univ funs measure uss)
      where
        uss = tss ++ [ts]
    loop m n tss us (t:ts) = do
      res <- explore t
      lift $ mapM_ present (result_props res)
      case res of
        Accepted _ ->
          loop m n tss (t:us) ts
        Rejected _ ->
          loop m n tss us ts

  evalStateT (loop 0 maxSize [] [] (moreTerms univ funs measure [])) state0
