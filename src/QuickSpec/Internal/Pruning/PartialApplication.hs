-- Pruning support for partial application and the like.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, RecordWildCards, MultiParamTypeClasses, FlexibleContexts, GeneralizedNewtypeDeriving, UndecidableInstances, DeriveFunctor #-}
module QuickSpec.Internal.Pruning.PartialApplication where

import QuickSpec.Internal.Term as Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Pruning.Background hiding (Pruner)
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Prop as Prop
import QuickSpec.Internal.Terminal
import QuickSpec.Internal.Testing
import Control.Monad.IO.Class
import Control.Monad.Trans.Class

data PartiallyApplied f =
    -- A partially-applied function symbol.
    -- The Int describes how many arguments the function expects.
    Partial f Int
    -- The ($) operator, for oversaturated applications.
    -- The type argument is the type of the first argument to ($).
  | Apply Type
  deriving (Eq, Ord, Functor)

instance Sized f => Sized (PartiallyApplied f) where
  size (Partial f _) = size f
  size (Apply _) = 1

instance Arity (PartiallyApplied f) where
  arity (Partial _ n) = n
  arity (Apply _) = 2

instance Pretty f => Pretty (PartiallyApplied f) where
  pPrint (Partial f n) = pPrint f <#> text "@" <#> pPrint n
  pPrint (Apply _) = text "$"

instance PrettyTerm f => PrettyTerm (PartiallyApplied f) where
  termStyle (Partial f _) = termStyle f
  termStyle (Apply _) = infixStyle 2

instance Typed f => Typed (PartiallyApplied f) where
  typ (Apply ty) = arrowType [ty] ty
  typ (Partial f _) = typ f
  otherTypesDL (Apply _) = mempty
  otherTypesDL (Partial f _) = otherTypesDL f
  typeSubst_ sub (Apply ty) = Apply (typeSubst_ sub ty)
  typeSubst_ sub (Partial f n) = Partial (typeSubst_ sub f) n

partial :: f -> Term (PartiallyApplied f)
partial f = Fun (Partial f 0)

total :: Arity f => f -> PartiallyApplied f
total f = Partial f (arity f)

smartApply ::
  Typed f => Term (PartiallyApplied f) -> Term (PartiallyApplied f) -> Term (PartiallyApplied f)
smartApply (Fun (Partial f n) :@: ts) u =
  Fun (Partial f (n+1)) :@: (ts ++ [u])
smartApply t u = simpleApply t u

simpleApply ::
  Typed f =>
  Term (PartiallyApplied f) -> Term (PartiallyApplied f) -> Term (PartiallyApplied f)
simpleApply t u =
  Fun (Apply (typ t)) :@: [t, u]

instance (Typed f, Background f) => Background (PartiallyApplied f) where
  background (Partial f _) =
    map (Prop.mapFun (\f -> Partial f arity)) (background f) ++
    [ simpleApply (partial n) (vs !! n) === partial (n+1)
    | n <- [0..arity-1] ]
    where
      arity = typeArity (typ f)
      partial i =
        Fun (Partial f i) :@: take i vs
      vs = map Var (zipWith V (typeArgs (typ f)) [0..])
  background _ = []

newtype Pruner fun pruner a =
  Pruner { run :: pruner a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner

instance (PrettyTerm fun, Typed fun, MonadPruner (Term (PartiallyApplied fun)) norm pruner) => MonadPruner (Term fun) norm (Pruner fun pruner) where
  normaliser =
    Pruner $ do
      norm <- normaliser
      return $ \t ->
        norm . encode $ t

  add prop =
    Pruner $ do
      add (encode <$> canonicalise prop)

  decodeNormalForm hole t =
    Pruner $ do
      t <- decodeNormalForm (fmap (fmap (flip Partial 0)) . hole) t
      let f (Partial x _) = NotId x
          f (Apply _) = Id
      return $ t >>= eliminateId . Term.mapFun f

encode :: Typed fun => Term fun -> Term (PartiallyApplied fun)
encode (Var x) = Var x
encode (Fun f) = partial f
encode (t :$: u) = smartApply (encode t) (encode u)
