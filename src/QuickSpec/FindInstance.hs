-- A module for building typeclass dictionaries at runtime.
-- Provides a data structure that, given a set of (possibly
-- polymorphic) functions and a target type, tries to construct a
-- value of that type.

{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module QuickSpec.FindInstance where

import Twee.Base
import QuickSpec.Type
import Data.MemoUgly
import Data.Functor.Identity
import Data.Maybe
import Data.Proxy
import Control.Monad

data Instances =
  Instances {
    is_construct :: Type -> [Value Identity],
    is_instances :: [Poly (Value Identity)] }

makeInstances :: [Poly (Value Identity)] -> Instances
makeInstances is = inst
  where
    inst = Instances (memo (constructUnmemoised inst)) is

instance Monoid Instances where
  mempty = makeInstances []
  x `mappend` y = makeInstances (is_instances x ++ is_instances y)

findInstance :: forall f. Typeable f => Instances -> Type -> [Value f]
findInstance insts ty =
  map (unwrapFunctor runIdentity) (is_construct insts ty')
  where
    ty' = typeRep (Proxy :: Proxy f) `applyType` ty

inst :: Typeable a => a -> Instances
inst x = instValue (toPolyValue x)

instValue :: Poly (Value Identity) -> Instances
instValue x =
  -- Transform x into a single-argument function.
  case typ x of
    App (F Arrow) (Cons _ (Cons (App (F Arrow) _) Empty)) ->
      instValue (apply uncur x)
    App (F Arrow) _ ->
      makeInstances [x]
    _ ->
      makeInstances [apply delay x]
  where
    uncur = toPolyValue (uncurry :: (A -> B -> C) -> (A, B) -> C)
    delay = toPolyValue ((\x () -> x) :: A -> () -> A)

-- invariant: returned value is a type instance of argument type
constructUnmemoised :: Instances -> Type -> [Value Identity]
constructUnmemoised _ (App (F unit) Empty)
  | unit == tyCon (Proxy :: Proxy ()) =
    return (toValue (Identity ()))
constructUnmemoised res (App (F pair) (Cons ty1 (Cons ty2 Empty)))
  | pair == tyCon (Proxy :: Proxy (,)) = do
    x <- is_construct res ty1
    sub <- maybeToList (match ty1 (typ x))
    y <- is_construct res (subst sub ty2)
    sub <- maybeToList (match ty2 (typ y))
    return (pairValues (liftM2 (,)) (typeSubst sub x) y)
constructUnmemoised insts ty = do
  -- Find a function whose result type unifies with ty.
  -- Rename it to avoid clashes with ty.
  fun <- fmap (polyRename ty) (is_instances insts)
  App (F Arrow) (Cons arg (Cons res Empty)) <- return (typ fun)
  sub <- maybeToList (unify ty res)
  fun <- return (typeSubst sub fun)
  arg <- return (typeSubst sub arg)
  -- Find an argument for that function and apply the function.
  val <- is_construct insts arg
  sub <- maybeToList (match arg (typ val))
  return (apply (typeSubst sub fun) val)
