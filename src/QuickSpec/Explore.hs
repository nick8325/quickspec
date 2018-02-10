{-# LANGUAGE FlexibleContexts #-}
module QuickSpec.Explore where

import QuickSpec.Explore.Polymorphic
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.Terminal
import QuickSpec.Prop
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import qualified Data.Set as Set
import Data.Set(Set)

baseTerms :: (Ord f, Typeable f, Ord a) => (Term f -> a) -> [f] -> [Term f]
baseTerms measure funs =
  sortBy' measure $
    [App f [] | f <- funs] ++
    [Var (V typeVar 0)]

moreTerms :: (Ord a, Apply (Term f)) => Set Type -> (Term f -> a) -> [[Term f]] -> [Term f]
moreTerms univ measure tss =
  sortBy' measure $
    [ unPoly v
    | i <- [0..n-1],
      t <- tss !! i,
      u <- tss !! (n-i),
      Just v <- [tryApply (poly t) (poly u)],
      and [ typ x `Set.member` univ | x <- subterms (unPoly v) ] ]
  where
    n = length tss

quickSpec ::
  (Ord measure, Ord fun, Typeable fun, Sized fun, Typed fun, Ord result, Apply (Term fun), PrettyTerm fun, PrettyArity fun,
   MonadPruner (Term fun) m, MonadTester testcase (Term fun) m) =>
  (Prop (Term fun) -> m ()) ->
  (Term fun -> measure) ->
  (Term fun -> testcase -> result) ->
  Int -> [fun] -> Type -> [Type] -> m ()
quickSpec present measure eval maxSize funs ty tys = withDefaultType ty $ do
  let
    univ = Set.fromList tys
    state0 = initialState tys (\t -> size t <= 5) eval

    loop 1 _ _ [] = return ()
    loop n tss ts [] =
      loop (n-1) uss [] (moreTerms univ measure uss)
      where
        uss = tss ++ [ts]
    loop n tss us (t:ts) = do
      res <- explore t
      lift $ mapM_ present (result_props res)
      case res of
        Accepted _ ->
          loop n tss (t:us) ts
        Rejected _ ->
          loop n tss us ts

  evalStateT (loop maxSize [[]] [] (baseTerms measure funs)) state0
