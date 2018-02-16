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
module QuickSpec.Explore.Conditionals where

import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Pruning
import QuickSpec.Pruning.Background(Background(..))
import QuickSpec.Testing
import QuickSpec.Terminal
import QuickSpec.Explore.PartialApplication
import qualified Twee.Base as Twee
import Data.List
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.IO.Class

newtype Conditionals m a = Conditionals { runConditionals :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)
instance MonadTrans Conditionals where
  lift = Conditionals
instance MonadPruner (Term (WithConstructor fun)) norm m =>
  MonadPruner (Term fun) norm (Conditionals m) where
  normaliser = lift $ do
    norm <- normaliser
    return (norm . fmap Normal)
  add prop = lift $ do
    add (mapFun Normal prop)

class Predicate fun where
  classify :: fun -> Classification fun

data Classification fun =
    Predicate { clas_selectors :: [fun], clas_test_case :: Type, clas_true :: Term fun }
  | Selector { clas_index :: Int, clas_pred :: fun, clas_test_case :: Type }
  | Function
  deriving (Eq, Ord, Functor)

instance (Arity fun, Predicate fun) => Predicate (PartiallyApplied fun) where
  classify f =
    case getTotal f of
      Nothing -> Function
      Just f -> fmap total (classify f)

data WithConstructor fun =
    Constructor fun Type
  | Normal fun
  deriving (Eq, Ord)

instance Sized fun => Sized (WithConstructor fun) where
  size Constructor{} = 0
  size (Normal f) = size f

instance Arity fun => Arity (WithConstructor fun) where
  arity Constructor{} = 1
  arity (Normal f) = arity f

instance Pretty fun => Pretty (WithConstructor fun) where
  pPrintPrec l p (Constructor f _) = pPrintPrec l p f <> text "_con"
  pPrintPrec l p (Normal f) = pPrintPrec l p f

instance PrettyTerm fun => PrettyTerm (WithConstructor fun) where
  termStyle (Constructor f _) = curried
  termStyle (Normal f) = termStyle f

instance PrettyArity fun => PrettyArity (WithConstructor fun) where
  prettyArity (Constructor f _) = 1
  prettyArity (Normal f) = prettyArity f

instance (Predicate fun, Background fun) => Background (WithConstructor fun) where
  background f@(Constructor pred _) =
    case classify pred of
      Predicate sels ty true ->
        let x = Var (V ty 0)
        in [App f [App (Normal sel) [x] | sel <- sels] === x,
            App (Normal pred) [App (Normal sel) [x] | sel <- sels] === fmap Normal true]
      _ -> error "constructor of non-predicate"
  background (Normal f) =
    map (mapFun Normal) (background f) ++
    case classify f of
      Predicate _ ty _ ->
        background (Constructor f ty)
      Selector _ pred ty ->
        background (Constructor pred ty)
      Function ->
        []

instance Typed fun => Typed (WithConstructor fun) where
  typ (Constructor pred ty) =
    arrowType (typeArgs (typ pred)) ty
  typ (Normal f) = typ f
  otherTypesDL (Constructor pred ty) = typesDL pred
  otherTypesDL (Normal f) = otherTypesDL f
  typeSubst_ sub (Constructor pred ty) = Constructor (typeSubst_ sub pred) (typeSubst_ sub ty)
  typeSubst_ sub (Normal f) = Normal (typeSubst_ sub f)

predType :: TyCon -> [Type] -> Type
predType name tys =
  Twee.build (Twee.app (Twee.fun name) tys)

considerConditionalising ::
  (Ord norm, MonadPruner (Term (WithConstructor fun)) norm m, Predicate fun) =>
  Term fun -> Prop (Term fun) -> Conditionals m ()
considerConditionalising true (lhs :=>: t :=: u) = do
  norm <- normaliser
  -- If we have discovered that "somePredicate x_1 x_2 ... x_n = True"
  -- we should add the axiom "get_x_n (toSomePredicate x_1 x_2 ... x_n) = x_n"
  -- to the set of known equations
  when (norm u == norm true) $
    case t of
      App f ts | Predicate{..} <- classify f -> do -- It is an interesting predicate, i.e. it was added by the user
        let ts' = map (fmap Normal) ts
            lhs' = map (fmap (fmap Normal)) lhs
            -- The "to_p x1 x2 ... xm" term
            construction = App (Constructor f clas_test_case) ts'
            -- The "p_n (to_p x1 x2 ... xn ... xm) = xn"
            -- equations
            equations = [ lhs' :=>: App (Normal (clas_selectors !! i)) [construction] :=: x | (x, i) <- zip ts' [0..]]

        -- Declare the relevant equations as axioms
        mapM_ (lift . add) equations
      _ -> return ()

conditionalise :: (Typed fun, Ord fun, Predicate fun) => Term fun -> Prop (Term fun) -> Prop (Term fun)
conditionalise true (lhs :=>: t :=: u) =
  go lhs t u
  where
    -- Replace one predicate selector with a conditional
    go lhs t u =
      case [ (v, i, p) | v@(App f [Var _]) <- subterms t ++ subterms u, Selector i p _ <- [classify f] ] of
        [] -> sort lhs :=>: t :=: u
        ((v, i, p):_) ->
          let
            n = freeVar [t, u]
            tys = typeArgs (typ p)
            xs = map Var (zipWith V tys [n..])
          in
            go ((App p xs :=: true):lhs) (replace v (xs !! i) t) (replace v (xs !! i) u)

    replace from to t
      | t == from = to
    replace from to (App f ts) =
      App f (map (replace from to) ts)
    replace _ _ (Var x) = Var x
