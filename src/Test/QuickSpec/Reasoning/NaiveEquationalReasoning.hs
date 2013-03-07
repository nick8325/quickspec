-- | Equational reasoning built on top of congruence closure.

{-# LANGUAGE CPP, TupleSections #-}
module Test.QuickSpec.Reasoning.NaiveEquationalReasoning where

#include "../errors.h"

import Test.QuickSpec.Term
import Test.QuickSpec.Equation
import Test.QuickSpec.Reasoning.CongruenceClosure(CC)
import qualified Test.QuickSpec.Reasoning.CongruenceClosure as CC
import Data.Map(Map)
import qualified Data.Map as Map
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import qualified Control.Monad.Trans.State.Strict as S
import Test.QuickSpec.Utils
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.Typeable
import Data.Ord
import Data.List

data Context = Context {
  rel :: CC.S,
  maxDepth :: Int,
  universe :: IntMap Universe
  }

type Universe = IntMap [Int]

type EQ = ReaderT (Int, IntMap Universe) CC

initial :: Int -> [Symbol] -> [Tagged Term] -> Context
initial d syms ts =
  let n = 1+maximum (0:map index syms)
      (universe, rel) =
        CC.runCC (CC.initial n) $
          forM (partitionBy (witnessType . tag) ts) $ \xs@(x:_) ->
            fmap (witnessType (tag x),) (createUniverse (map erase xs))
      univMap = Map.fromList universe

  in Context rel d . IntMap.fromList $ [
    (index sym,
     Map.findWithDefault IntMap.empty (symbolType sym) univMap)
    | sym <- syms ]

createUniverse :: [Term] -> CC Universe
createUniverse ts = fmap IntMap.fromList (mapM createTerms tss)
  where tss = partitionBy depth ts
        createTerms ts@(t:_) = fmap (depth t,) (mapM flatten ts)

runEQ :: Context -> EQ a -> (a, Context)
runEQ ctx x = (y, ctx { rel = rel' })
  where (y, rel') = runState (runReaderT x (maxDepth ctx, universe ctx)) (rel ctx)

evalEQ :: Context -> EQ a -> a
evalEQ ctx x = fst (runEQ ctx x)

execEQ :: Context -> EQ a -> Context
execEQ ctx x = snd (runEQ ctx x)

liftCC :: CC a -> EQ a
liftCC x = ReaderT (const x)

(=?=) :: Term -> Term -> EQ Bool
t =?= u = liftCC $ do
  x <- flatten t
  y <- flatten u
  x CC.=?= y

equal :: Equation -> EQ Bool
equal (t :=: u) = t =?= u

(=:=) :: Term -> Term -> EQ Bool
t =:= u = unify (t :=: u)

unify :: Equation -> EQ Bool
unify (t :=: u) = do
  (d, ctx) <- ask
  b <- t =?= u
  unless b $
    forM_ (substs t ctx d ++ substs u ctx d) $ \s -> liftCC $ do
      t' <- subst s t
      u' <- subst s u
      t' CC.=:= u'
  return b

type Subst = Symbol -> Int

substs :: Term -> IntMap Universe -> Int -> [Subst]
substs t univ d = map lookup (sequence (map choose vars))
  where vars = map (maximumBy (comparing snd)) .
               partitionBy fst .
               holes $ t

        choose (x, n) =
          let m = IntMap.findWithDefault (ERROR "empty universe")
                  (index x) univ in
          [ (x, t)
          | d' <- [0..d-n],
            t <- IntMap.findWithDefault [] d' m ]

        lookup ss =
          let m = IntMap.fromList [ (index x, y) | (x, y) <- ss ]
          in \x -> IntMap.findWithDefault (index x) (index x) m

subst :: Subst -> Term -> CC Int
subst s (Var x) = return (s x)
subst s (Const x) = return (index x)
subst s (App f x) = do
  f' <- subst s f
  x' <- subst s x
  f' CC.$$ x'

flatten :: Term -> CC Int
flatten = subst index

get :: EQ CC.S
get = liftCC S.get

put :: CC.S -> EQ ()
put x = liftCC (S.put x)

rep :: Term -> EQ Int
rep x = liftCC (flatten x >>= CC.rep)
