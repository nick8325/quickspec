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

import QuickSpec.Internal.Prop
import QuickSpec.Internal.Term
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
instance (Typed fun, Ord fun, PrettyTerm fun, Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun, MonadTerminal m) =>
  MonadPruner (Term fun) norm (Conditionals m) where
  normaliser = lift $ do
    norm <- normaliser
    return (norm . fmap Normal)
  add prop = do
    redundant <- conditionallyRedundant prop
    if redundant then return False else do
      res <- lift (add (mapFun Normal prop))
      when res (considerConditionalising prop)
      return res

conditionalsUniverse :: (Typed fun, Predicate fun) => [Type] -> [fun] -> Universe
conditionalsUniverse tys funs =
  universe $
    tys ++
    (map typ $
      map Normal funs ++
      [ Constructor pred clas_test_case | pred <- funs, Predicate{..} <- [classify pred] ])

runConditionals ::
  (PrettyTerm fun, Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun, MonadTerminal m) =>
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

data WithConstructor fun =
    Constructor fun Type
  | Normal fun
  deriving (Eq, Ord)

instance Sized fun => Sized (WithConstructor fun) where
  size Constructor{} = 0
  size (Normal f) = size f

instance Pretty fun => Pretty (WithConstructor fun) where
  pPrintPrec l p (Constructor f _) = pPrintPrec l p f <#> text "_con"
  pPrintPrec l p (Normal f) = pPrintPrec l p f

instance PrettyTerm fun => PrettyTerm (WithConstructor fun) where
  termStyle (Constructor _ _) = curried
  termStyle (Normal f) = termStyle f

instance (Predicate fun, Background fun) => Background (WithConstructor fun) where
  background (Normal f) = map (mapFun Normal) (background f)
  background _ = []

instance Typed fun => Typed (WithConstructor fun) where
  typ (Constructor pred ty) =
    arrowType (typeArgs (typ pred)) ty
  typ (Normal f) = typ f
  otherTypesDL (Constructor pred _) = typesDL pred
  otherTypesDL (Normal f) = otherTypesDL f
  typeSubst_ sub (Constructor pred ty) = Constructor (typeSubst_ sub pred) (typeSubst_ sub ty)
  typeSubst_ sub (Normal f) = Normal (typeSubst_ sub f)

predType :: TyCon -> [Type] -> Type
predType name tys =
  Twee.build (Twee.app (Twee.fun name) tys)

considerPredicate ::
  (PrettyTerm fun, Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun, MonadTerminal m) =>
  fun -> Conditionals m ()
considerPredicate f =
  case classify f of
    Predicate sels ty true -> do
      let
        x = Var (V ty 0)
        eqns =
          [Fun (Constructor f ty) :@: [Fun (Normal sel) :$: x | sel <- sels] === x,
           Fun (Normal f) :@: [Fun (Normal sel) :$: x | sel <- sels] === fmap Normal true]
      mapM_ (lift . add) eqns
    _ -> return ()

considerConditionalising ::
  (Typed fun, Ord fun, PrettyTerm fun, Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun, MonadTerminal m) =>
  Prop (Term fun) -> Conditionals m ()
considerConditionalising (lhs :=>: t :=: u) = do
  norm <- normaliser
  -- If we have discovered that "somePredicate x_1 x_2 ... x_n = True"
  -- we should add the axiom "get_x_n (toSomePredicate x_1 x_2 ... x_n) = x_n"
  -- to the set of known equations
  case t of
    Fun f :@: ts | Predicate{..} <- classify f -> -- It is an interesting predicate, i.e. it was added by the user
      when (norm u == norm clas_true) $
        addPredicate lhs f ts
    _ -> return ()

conditionallyRedundant ::
  (Typed fun, Ord fun, PrettyTerm fun, Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun, MonadTerminal m) =>
  Prop (Term fun) -> Conditionals m Bool
conditionallyRedundant (lhs :=>: t :=: u) = do
  t' <- normalise t
  u' <- normalise u
  conditionallyRedundant' lhs t u t' u'

conditionallyRedundant' ::
  (Typed fun, Ord fun, PrettyTerm fun, Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun, MonadTerminal m) =>
  [Equation (Term fun)] -> Term fun -> Term fun -> norm -> norm -> Conditionals m Bool
conditionallyRedundant' lhs t u t' u' = do
  forM_ (usort (funs [t, u])) $ \f ->
    case classify f of
      Selector{..} -> do
        let
          Predicate{..} = classify clas_pred
          tys = typeArgs (typ clas_pred)
          argss = sequence [ [ arg | arg <- terms [t, u] >>= subterms, typ arg == ty ] | ty <- tys ]
        forM_ argss $ \args -> do
          norm <- normaliser
          let p = Fun clas_pred :@: args
          when (norm p == norm clas_true) $ do
            addPredicate lhs clas_pred args
      _ -> return ()

  t'' <- normalise t
  u'' <- normalise u
  if t'' == u'' then
    return True
   else if t'' == t' && u'' == u' then
     return False
    else
     conditionallyRedundant' lhs t u t'' u''

addPredicate ::
  (PrettyTerm fun, Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun, MonadTerminal m) =>
  [Equation (Term fun)] -> fun -> [Term fun] -> Conditionals m ()
addPredicate lhs f ts = do
  let Predicate{..} = classify f
      ts' = map (fmap Normal) ts
      lhs' = map (fmap (fmap Normal)) lhs
      -- The "to_p x1 x2 ... xm" term
      construction = Fun (Constructor f clas_test_case) :@: ts'
      -- The "p_n (to_p x1 x2 ... xn ... xm) = xn"
      -- equations
      equations = [ lhs' :=>: Fun (Normal (clas_selectors !! i)) :$: construction :=: x | (x, i) <- zip ts' [0..]]

  -- Declare the relevant equations as axioms
  mapM_ (lift . add) equations

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
