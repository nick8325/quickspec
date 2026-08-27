-- Encode conditionals during pruning.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, UndecidableInstances, DeriveGeneric #-}
module QuickSpec.Internal.Pruning.Conditionals where

import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Pruning.Background(Background(..))
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Prop hiding (mapFun)
import QuickSpec.Internal.Terminal
import QuickSpec.Internal.Utils
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import GHC.Generics
import Data.Hashable
import Data.Hashable.Generic

data Conditionals fun =
    Func fun
  | Guard Type (UnconditionalTerm fun) (UnconditionalTerm fun) (UnconditionalTerm fun) (UnconditionalTerm fun) [Var]
  deriving (Eq, Ord, Show, Typeable, Generic)

instance Hashable fun => Hashable (Conditionals fun) where
  hashWithSalt = genericHashWithSalt

instance Arity fun => Arity (Conditionals fun) where
  arity (Func f) = arity f
  arity (Guard _ _ _ _ _ vs) = length vs + 1

instance Sized fun => Sized (Conditionals fun) where
  size (Func f) = size f
  size Guard{} = 0

instance Sized fun => FuncSized (Conditionals fun) where
  -- Note: since there is no FuncSized instance for PartiallyApplied
  -- we just assume that Func f is adding the size of its arguments
  sizeApp (Func f) ts = size f + sum ts
  sizeApp Guard{} ts = penalty + maximum ts
    where
      penalty = 3

instance Pretty fun => Pretty (Conditionals fun) where
  pPrint (Func f) = pPrint f
  pPrint Guard{} = text "guard"

instance PrettyTerm fun => PrettyTerm (Conditionals fun) where
  termStyle (Func f) = termStyle f
  termStyle Guard{} = uncurried

instance Typed fun => Typed (Conditionals fun) where
  typ (Func f) = typ f
  typ (Guard ty t _ _ _ vs) = arrowType (typ t:map typ vs) ty

  typeSubst_ sub (Func f) = Func (typeSubst_ sub f)
  typeSubst_ sub (Guard ty t u v w vs) = Guard (typeSubst_ sub ty) (typeSubst_ sub t) (typeSubst_ sub u) (typeSubst_ sub v) (typeSubst_ sub w) (typeSubst_ sub vs)

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

  add prop = and <$> lift (mapM add (conditionalise' (canonicalise prop)))

  decodeNormalForm hole t =
    Pruner $ do
      t <- decodeNormalForm (fmap (fmap Func) . hole) t
      let elimIfEq (Func f) = Just f
          elimIfEq Guard{} = Nothing
      return $ t >>= mapFunM elimIfEq

instance (Typed fun, Arity fun, Background fun) => Background (Conditionals fun) where
  background (Func f) = concatMap conditionalise' (background f)
  background Guard{} = []

conditionalise :: Typed fun => Prop (UnconditionalTerm fun) -> [Prop (UnconditionalTerm fun)]
conditionalise prop@([] :=>: _) = [prop]
conditionalise ((t :=: u):lhs :=>: v :=: w) =
  ([] :=>: guarded t v):conditionalise (lhs :=>: guarded u w)
  where
    guarded x y = Fun (Guard ty t u v w vs) :@: (x:map Var vs) :=: y
    vs = usort (concatMap vars [t, u, v, w])
    ty = typ t

conditionalise' :: Typed fun => Prop (ConditionalTerm fun) -> [Prop (UnconditionalTerm fun)]
conditionalise' = conditionalise . mapTerm (mapFun Func)
