-- Pruning support for partial application and the like.
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, RecordWildCards, MultiParamTypeClasses, FlexibleContexts, GeneralizedNewtypeDeriving, UndecidableInstances #-}
module QuickSpec.Explore.PartialApplication where

import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Prop
import qualified Twee.Base as Twee
import qualified Data.Set as Set
import Data.Set(Set)
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict hiding (State)

data PartiallyApplied f =
    -- A partially-applied function symbol.
    -- The Int describes how many arguments the function expects.
    Partial f Int
    -- The ($) operator, for oversaturated applications.
    -- The type argument is the type of the first argument to ($).
  | Apply Type
  deriving (Eq, Ord)

instance Sized f => Sized (PartiallyApplied f) where
  size (Partial f _) = size f
  size (Apply _) = 0

instance Arity f => Arity (PartiallyApplied f) where
  arity (Partial _ n) = n
  arity (Apply _) = 2

instance Pretty f => Pretty (PartiallyApplied f) where
  pPrint (Partial f _) = pPrint f
  pPrint (Apply _) = text "$"

instance PrettyTerm f => PrettyTerm (PartiallyApplied f) where
  termStyle (Partial f _) = termStyle f
  termStyle (Apply _) = invisible

instance Typed f => Typed (PartiallyApplied f) where
  typ (Apply ty) = Twee.build (Twee.app (Twee.fun Arrow) [ty, ty])
  typ (Partial f _) = typ f
  otherTypesDL (Apply _) = mempty
  otherTypesDL (Partial f _) = otherTypesDL f
  typeSubst_ sub (Apply ty) = Apply (typeSubst_ sub ty)
  typeSubst_ sub (Partial f n) = Partial (typeSubst_ sub f) n

instance (Arity f, Ord f, Typeable f, Typed f) => Apply (Term (PartiallyApplied f)) where
  tryApply t u = do
    tryApply (typ t) (typ u)
    return $
      case t of
        -- App (Partial f n) ts | n < arity f ->
        --   App (Partial f (n+1)) (ts ++ [u])
        _ ->
          simpleApply t u

simpleApply ::
  (Arity f, Ord f, Typeable f, Typed f) =>
  Term (PartiallyApplied f) -> Term (PartiallyApplied f) -> Term (PartiallyApplied f)
simpleApply t u =
  App (Apply (typ t)) [t, u]

newtype EncodePartialApplications f m a =
  EncodePartialApplications (StateT (Set f) m a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (EncodePartialApplications f) where
  lift = EncodePartialApplications . lift

runEncodePartialApplications :: Monad m => EncodePartialApplications f m a -> m a
runEncodePartialApplications (EncodePartialApplications x) =
  evalStateT x Set.empty

instance (Ord f, Arity f, Typeable f, Typed f, Pruner (Term (PartiallyApplied f)) m) =>
  Pruner (Term (PartiallyApplied f)) (EncodePartialApplications f m) where
  normaliser = lift normaliser
  add prop = do
    mapM_ addFunction (funs prop)
    lift (add prop)

instance Tester testcase term m => Tester testcase term (EncodePartialApplications f m) where
  test = lift . test

addFunction :: (Ord f, Typed f, Arity f, Typeable f, Pruner (Term (PartiallyApplied f)) m) =>
  PartiallyApplied f -> EncodePartialApplications f m ()
-- addFunction (Partial f _) = EncodePartialApplications $ do
--   funcs <- get
--   unless (f `Set.member` funcs) $ do
--     put (Set.insert f funcs)
--     mapM_ (lift . add) (axioms f)
--     where
--       axioms f =
--         [ simpleApply (partial i) (vs !! i) === partial (i+1)
--         | i <- [0..arity f-1] ]
--       partial i =
--         App (Partial f i) (take i vs)
--       vs = map Var (zipWith V (typeArgs (typ f)) [0..])
addFunction _ = return ()

instance (Applicative f, Eval fun (Value f)) => Eval (PartiallyApplied fun) (Value f) where
  eval var (Partial f _) = eval var f
  eval _ (Apply ty) =
    fromJust $
      cast (Twee.build (Twee.app (Twee.fun Arrow) [ty, ty]))
        (toValue (pure (($) :: (A -> B) -> (A -> B))))
