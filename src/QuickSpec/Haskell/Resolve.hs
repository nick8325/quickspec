-- A data structure for resolving typeclass instances and similar at runtime.
--
-- Takes as input a set of functions ("instances"), and a type, and
-- tries to build a value of that type from the instances given.
--
-- For example, given the instances
--   ordList :: Dict (Arbitrary a) -> Dict (Arbitrary [a])
--   ordChar :: Dict (Arbitrary Char)
-- and the target type Dict (Arbitrary [Char]), it will produce the value
--   ordList ordChar :: Dict (Arbitrary [Char]).
--
-- The instances can in fact be arbitrary Haskell functions - though
-- their types must be such that the instance search will terminate.

{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module QuickSpec.Haskell.Resolve(Instances(..), inst, valueInst, findInstance, findValue) where

import Twee.Base
import QuickSpec.Type
import Data.MemoUgly
import Data.Functor.Identity
import Data.Maybe
import Data.Proxy
import Control.Monad

-- A set of instances.
data Instances =
  Instances {
    -- The available instances.
    -- Each instance is a unary function; 'inst' sees to this.
    is_instances :: [Poly (Value Identity)],
    -- The resulting instance search function (memoised).
    is_find      :: Type -> [Value Identity] }

-- A smart constructor for Instances.
makeInstances :: [Poly (Value Identity)] -> Instances
makeInstances is = inst
  where
    inst = Instances is (memo (find_ inst . canonicaliseType))

instance Monoid Instances where
  mempty = makeInstances []
  x `mappend` y = makeInstances (is_instances x ++ is_instances y)

-- Create a single instance.
inst :: Typeable a => a -> Instances
inst x = valueInst (toValue (Identity x))

valueInst :: Value Identity -> Instances
valueInst x = polyInst (poly x)
  where
    polyInst :: Poly (Value Identity) -> Instances
    polyInst x =
      -- Transform x into a single-argument function
      -- (see comment about is_instances).
      case typ x of
        -- A function of type a -> (b -> c) gets uncurried.
        App (F Arrow) (Cons _ (Cons (App (F Arrow) _) Empty)) ->
          polyInst (apply uncur x)
        App (F Arrow) _ ->
          makeInstances [x]
        -- A plain old value x (not a function) turns into \() -> x.
        _ ->
          makeInstances [apply delay x]
      where
        uncur = toPolyValue (uncurry :: (A -> B -> C) -> (A, B) -> C)
        delay = toPolyValue ((\x () -> x) :: A -> () -> A)

-- Construct a value of a particular type.
-- If the type is polymorphic, may return an instance of it.
findValue :: Instances -> Type -> Maybe (Value Identity)
findValue insts = listToMaybe . is_find insts . skolemiseTypeVars

-- Given a type a, construct a value of type f a.
-- If the type is polymorphic, may return an instance of it.
findInstance :: forall f. Typeable f => Instances -> Type -> Maybe (Value f)
findInstance insts ty =
  unwrapFunctor runIdentity <$> findValue insts ty'
  where
    ty' = typeRep (Proxy :: Proxy f) `applyType` ty

-- The unmemoised version of the search algorithm.
-- Knows how to apply unary functions, and also knows how to generate:
--   * The unit type ()
--   * Pairs (a, b) - search for a and then for b
-- These two are important because instValue encodes other instances
-- using them.
--
-- Invariant: the type of the returned value is an instance of the argument type.
find_ :: Instances -> Type -> [Value Identity]
find_ _ (App (F unit) Empty)
  | unit == tyCon (Proxy :: Proxy ()) =
    return (toValue (Identity ()))
find_ insts (App (F pair) (Cons ty1 (Cons ty2 Empty)))
  | pair == tyCon (Proxy :: Proxy (,)) = do
    x <- is_find insts ty1
    sub <- maybeToList (match ty1 (typ x))
    -- N.B.: subst sub ty2 because searching for x may have constrained y's type
    y <- is_find insts (subst sub ty2)
    sub <- maybeToList (match ty2 (typ y))
    return (pairValues (liftM2 (,)) (typeSubst sub x) y)
find_ insts ty = do
  -- Find a function whose result type unifies with ty.
  -- Rename it to avoid clashes with ty.
  fun <- fmap (polyRename ty) (is_instances insts)
  App (F Arrow) (Cons arg (Cons res Empty)) <- return (typ fun)
  sub <- maybeToList (unify ty res)
  fun <- return (typeSubst sub fun)
  arg <- return (typeSubst sub arg)
  -- Find an argument for that function and apply the function.
  val <- is_find insts arg
  sub <- maybeToList (match arg (typ val))
  return (apply (typeSubst sub fun) val)
