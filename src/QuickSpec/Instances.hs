-- A module for building typeclass dictionaries at runtime.
-- Provides a data structure that, given a set of (possibly
-- polymorphic) functions and a target type, tries to construct a
-- value of that type.

{-# LANGUAGE RankNTypes, CPP, ScopedTypeVariables #-}
module QuickSpec.Instances where

#include "errors.h"
import Twee.Base
import QuickSpec.Type
import Data.Monoid
import Data.MemoUgly
import Data.Functor.Identity
import Data.Maybe
import Control.Monad

data Instances =
  Instances {
    is_construct :: Type -> [Value Identity],
    is_instances :: [Poly (Value Identity)] }

makeInstances :: [Poly (Value Identity)] -> Instances
makeInstances is = inst
  where
    inst = Instances (memo (construct_ inst)) is

instance Monoid Instances where
  mempty = makeInstances []
  x `mappend` y = makeInstances (is_instances x ++ is_instances y)

findInstance :: forall f. Typeable f => Instances -> Type -> [Value f]
findInstance insts ty =
  map (unwrapFunctor runIdentity) (is_construct insts ty')
  where
    ty' = typeRep (undefined :: proxy f) `applyType` ty

inst :: Typeable a => a -> Instances
inst x = instValue (polyValue x)

instValue :: Poly (Value Identity) -> Instances
instValue x =
  -- Transform x into a single-argument function.
  case typ x of
    App Arrow [_, App Arrow _] ->
      instValue (apply uncur x)
    App Arrow _ ->
      makeInstances [x]
    _ ->
      makeInstances [apply delay x]
  where
    uncur = polyValue (uncurry :: (A -> B -> C) -> (A, B) -> C)
    delay = polyValue ((\x () -> x) :: A -> () -> A)

polyValue :: Typeable a => a -> Poly (Value Identity)
polyValue = poly . toValue . Identity

construct_ :: Instances -> Type -> [Value Identity]
construct_ _ (App unit [])
  | unit == tyCon () =
    return (toValue (Identity ()))
construct_ res (App pair [ty1, ty2])
  | pair == tyCon ((),()) = do
    x <- findInstance res ty1
    y <- findInstance res ty2
    return (pairValues (liftM2 (,)) x y)
construct_ insts ty = do
  -- Find a function whose result type unifies with ty.
  -- Rename it to avoid clashes with ty.
  fun <- fmap (polyRename ty) (is_instances insts)
  App Arrow [arg, res] <- return (typ fun)
  sub <- maybeToList (unify ty res)
  arg <- return (typeSubst sub arg)
  -- Find an argument for that function and apply the function.
  val <- construct_ insts arg
  return (unPoly (apply (poly fun) (poly val)))
