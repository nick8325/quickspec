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
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Text.Printf

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
  Int -> Universe -> [fun] -> m ()
quickSpec present measure eval maxSize univ funs = do
  let
    state0 = initialState univ (\t -> size t <= 5) eval

    loop m n _ | m > n = return ()
    loop m n tss = do
      putStatus (printf "enumerating terms of size %d" m)
      let
        ts = moreTerms univ funs measure tss
        total = length ts
        consider (i, t) = do
          putStatus (printf "testing terms of size %d: %d/%d" m i total)
          res <- explore t
          putStatus (printf "testing terms of size %d: %d/%d" m i total)
          lift $ mapM_ present (result_props res)
          case res of
            Accepted _ -> return True
            Rejected _ -> return False
      us <- map snd <$> filterM consider (zip [1 :: Int ..] ts)
      clearStatus
      loop (m+1) n (tss ++ [us])

  evalStateT (loop 0 maxSize []) state0
