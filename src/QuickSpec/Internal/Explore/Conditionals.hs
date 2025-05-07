{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
module QuickSpec.Internal.Explore.Conditionals where

import QuickSpec.Internal.Prop as Prop
import QuickSpec.Internal.Term as Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Pruning.Background(Background(..))
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Terminal
import QuickSpec.Internal.Utils
import QuickSpec.Internal.Explore.Polymorphic
import qualified Twee.Base as Twee
import Data.List
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.IO.Class

newtype Conditionals m a = Conditionals (m a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)
instance MonadTrans Conditionals where
  lift = Conditionals
instance (Typed fun, Ord fun, PrettyTerm fun, Ord norm, MonadPruner (Term fun) norm m, Predicate fun, MonadTerminal m) =>
  MonadPruner (Term fun) norm (Conditionals m) where
  normaliser = lift normaliser
  add = lift . add . conditionalise
  decodeNormalForm hole t = lift (decodeNormalForm hole t)

conditionalsUniverse :: (Typed fun, Predicate fun) => [Type] -> [fun] -> Universe
conditionalsUniverse tys funs =
  universe $
    tys ++
    (map typ funs)
      -- map Normal funs) -- ++
      -- [ Constructor pred clas_test_case | pred <- funs, Predicate{..} <- [classify pred] ])

runConditionals ::
  (PrettyTerm fun, Ord norm, MonadPruner (Term fun) norm m, Predicate fun, MonadTerminal m) =>
  [fun] -> Conditionals m a -> m a
runConditionals preds mx =
  run (mapM_ considerPredicate preds >> mx)
  where
    run (Conditionals mx) = mx

class Predicate fun where
  classify :: fun -> Classification fun

data Classification fun =
    Predicate { clas_selectors :: [fun], clas_test_case :: Type, clas_true :: Term fun }
  | Selector { clas_index :: Int, clas_pred :: fun, clas_test_case :: Type }
  | Function
  deriving (Eq, Ord, Functor)

{-
data WithConstructor fun =
    Constructor fun Type
  | Normal fun
  deriving (Eq, Ord)
-}

predType :: TyCon -> [Type] -> Type
predType name tys =
  Twee.build (Twee.app (Twee.fun name) tys)

considerPredicate ::
  (PrettyTerm fun, Ord norm, MonadPruner (Term fun) norm m, Predicate fun, MonadTerminal m) =>
  fun -> Conditionals m ()
considerPredicate f =
  case classify f of
    Predicate sels ty true -> do
      let
        x = Var (V ty 0)
        eqns =
          [Fun f :@: [Fun sel :$: x | sel <- sels] === true]
      mapM_ (lift . add) eqns
    _ -> return ()

considerConditionalising ::
  (Typed fun, Ord fun, PrettyTerm fun, Ord norm, MonadPruner (Term fun) norm m, Predicate fun, MonadTerminal m) =>
  Prop (Term fun) -> Conditionals m ()
considerConditionalising (lhs :=>: t :=: u) = return ()

conditionalise :: (PrettyTerm fun, Typed fun, Ord fun, Predicate fun) => Prop (Term fun) -> Prop (Term fun)
conditionalise (lhs :=>: t :=: u) =
  go lhs t u
  where
    -- Replace one predicate with a conditional
    go lhs t u =
      case [ (p, x, clas_selectors, clas_true) | Fun f :$: Var x <- subterms t ++ subterms u, Selector _ p _ <- [classify f], Predicate{..} <- [classify p] ] of
        [] -> sort lhs :=>: t :=: u
        ((p, x, sels, true):_) ->
          let
            n = freeVar [t, u]
            tys = typeArgs (typ p)
            xs = map Var (zipWith V tys [n..])
            subs = [(Fun (sels !! i) :$: Var x, xs !! i) | i <- [0..length tys-1]]
          in
            go ((Fun p :@: xs :=: true):lhs) (replaceMany subs t) (replaceMany subs u)

    replace from to t
      | t == from = to
    replace from to (t :$: u) =
      replace from to t :$: replace from to u
    replace _ _ (Var x) = Var x
    replace _ _ (Fun f) = Fun f

    replaceMany subs t =
      foldr (uncurry replace) t subs

