-- Pruning support for partial application and the like.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, RecordWildCards, MultiParamTypeClasses, FlexibleContexts, GeneralizedNewtypeDeriving, UndecidableInstances, DeriveFunctor #-}
module QuickSpec.Internal.Explore.PartialApplication where

import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Pruning.Background
import QuickSpec.Internal.Prop
import qualified Twee.Base as Twee
import Data.Maybe

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
  pPrint (Partial f _) = pPrint f
  pPrint (Apply _) = text "$"

instance PrettyTerm f => PrettyTerm (PartiallyApplied f) where
  termStyle (Partial f _) = termStyle f
  termStyle (Apply _) = invisible

instance PrettyArity f => PrettyArity (PartiallyApplied f) where
  prettyArity (Partial f _) = prettyArity f
  prettyArity (Apply _) = 1

instance Typed f => Typed (PartiallyApplied f) where
  typ (Apply ty) = arrowType [ty] ty
  typ (Partial f _) = typ f
  otherTypesDL (Apply _) = mempty
  otherTypesDL (Partial f _) = otherTypesDL f
  typeSubst_ sub (Apply ty) = Apply (typeSubst_ sub ty)
  typeSubst_ sub (Partial f n) = Partial (typeSubst_ sub f) n

instance (Arity f, Typed f) => Apply (Term (PartiallyApplied f)) where
  tryApply t u = do
    tryApply (typ t) (typ u)
    return $
      case t of
        App (Partial f n) ts | n < arity f ->
          App (Partial f (n+1)) (ts ++ [u])
        _ ->
          simpleApply t u

getTotal :: Arity f => PartiallyApplied f -> Maybe f
getTotal (Partial f n) | arity f == n = Just f
getTotal _ = Nothing

partial :: f -> Term (PartiallyApplied f)
partial f = App (Partial f 0) []

total :: Arity f => f -> PartiallyApplied f
total f = Partial f (arity f)

simpleApply ::
  Typed f =>
  Term (PartiallyApplied f) -> Term (PartiallyApplied f) -> Term (PartiallyApplied f)
simpleApply t u =
  App (Apply (typ t)) [t, u]

instance (Arity f, Typed f, Background f) => Background (PartiallyApplied f) where
  background (Partial f _) =
    map (mapFun (\f -> Partial f (arity f))) (background f) ++
    [ simpleApply (partial n) (vs !! n) === partial (n+1)
    | n <- [0..arity f-1] ]
    where
      partial i =
        App (Partial f i) (take i vs)
      vs = map Var (zipWith V (typeArgs (typ f)) [0..])
  background _ = []

evalPartiallyApplied ::
  (Applicative f, Monad m) =>
  (fun -> m (Value f)) ->
  (PartiallyApplied fun -> m (Value f))
evalPartiallyApplied eval (Partial f _) = eval f
evalPartiallyApplied _ (Apply ty) =
  return $ fromJust $
    cast (Twee.build (Twee.app (Twee.fun Arrow) [ty, ty]))
      (toValue (pure (($) :: (A -> B) -> (A -> B))))
