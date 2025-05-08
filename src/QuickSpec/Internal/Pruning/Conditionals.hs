-- Encode conditionals during pruning.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
module QuickSpec.Internal.Pruning.Conditionals where

import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Pruning.Background(Background(..))
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Prop hiding (mapFun)
import QuickSpec.Internal.Terminal
import Control.Monad.IO.Class
import Control.Monad.Trans.Class

data Conditionals fun =
    Func fun
  | IfEq Type Type
  deriving (Eq, Ord, Show, Typeable)

instance Arity fun => Arity (Conditionals fun) where
  arity (Func f) = arity f
  arity (IfEq _ _) = 4

instance Sized fun => Sized (Conditionals fun) where
  size (Func f) = size f
  size (IfEq _ _) = 0
  sizeMode (Func f) = sizeMode f
  sizeMode (IfEq _ _) = MaxArgs

instance Pretty fun => Pretty (Conditionals fun) where
  pPrint (Func f) = pPrint f
  pPrint (IfEq _ _) = text "ifeq"

instance PrettyTerm fun => PrettyTerm (Conditionals fun) where
  termStyle (Func f) = termStyle f
  termStyle (IfEq _ _) = uncurried

instance Typed fun => Typed (Conditionals fun) where
  typ (Func f) = typ f
  typ (IfEq ty1 ty2) = arrowType [ty1, ty1, ty2, ty2] ty2

  typeSubst_ sub (Func f) = Func (typeSubst_ sub f)
  typeSubst_ sub (IfEq ty1 ty2) = IfEq (typeSubst_ sub ty1) (typeSubst_ sub ty2)

instance EqualsBonus (Conditionals fun) where

type ConditionalTerm fun = Term fun
type UnconditionalTerm fun = Term (Conditionals fun)

newtype Pruner fun pruner a =
  Pruner { run :: pruner a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner

instance (PrettyTerm fun, Typed fun, MonadPruner (UnconditionalTerm fun) norm pruner) => MonadPruner (ConditionalTerm fun) norm (Pruner fun pruner) where
  normaliser =
    Pruner $ do
      norm <- normaliser :: pruner (UnconditionalTerm fun -> norm)

      return $ \t ->
        norm . mapFun Func $ t

  add prop = lift (add (conditionalise (canonicalise prop)))

  decodeNormalForm hole t =
    Pruner $ do
      t <- decodeNormalForm (fmap (fmap Func) . hole) t
      let elimIfEq (Func f) = Just f
          elimIfEq (IfEq _ _) = Nothing
      return $ t >>= mapFunM elimIfEq

instance (Typed fun, Arity fun, Background fun) => Background (Conditionals fun) where
  background (Func f) =
    map conditionalise (background f)
  background f@(IfEq ty1 ty2) =
    [ Fun f :@: [x, x, y, z] === y ]
    where
      x = Var (V ty1 0)
      y = Var (V ty2 1)
      z = Var (V ty2 2)

conditionalise :: Typed fun => Prop (ConditionalTerm fun) -> Prop (UnconditionalTerm fun)
conditionalise prop@([] :=>: _) = mapTerm (mapFun Func) prop
conditionalise ((t :=: u):lhs :=>: rhs) =
  Fun (IfEq ty1 ty2) :@: [mapFun Func t, mapFun Func u, v, w] === w
  where
    [] :=>: v :=: w = conditionalise (lhs :=>: rhs)
    ty1 = typ t
    ty2 = typ v
