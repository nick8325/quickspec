{-# LANGUAGE TupleSections #-}
module NaiveEquationalReasoning where

import Term
import CongruenceClosure(CC)
import qualified CongruenceClosure as CC
import Data.Map(Map)
import qualified Data.Map as Map
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Utils
import Typed
import Typeable
import Data.Ord
import Data.List

data Context = Context {
  rel :: CC.S,
  universe :: Map TypeRep Universe,
  maxDepth :: Int
  }

type Universe = IntMap [Int]

type EQ = ReaderT (Map TypeRep Universe, Int) CC

initial :: Int -> [Typed Term] -> Context
initial d ts =
  let n = 1+maximum (0:concatMap (map index . symbols . erase) ts)
      (universe, rel) =
        CC.runCC (CC.initial n) $
          forM (partitionBy (some (typeOf . witness) . typ) ts) $ \xs@(x:_) ->
            fmap (some (typeOf . witness) (typ x),) (createUniverse (map erase xs))
      
  in Context rel (Map.fromList universe) d

createUniverse :: [Term] -> CC Universe
createUniverse ts = fmap IntMap.fromList (mapM createTerms tss)
  where tss = partitionBy depth ts
        createTerms ts@(t:_) = fmap (depth t,) (mapM flatten ts)

runEQ :: Context -> EQ a -> (a, Context)
runEQ ctx x = (y, ctx { rel = rel' })
  where (y, rel') = runState (runReaderT x (universe ctx, maxDepth ctx)) (rel ctx)

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

(=:=) :: Term -> Term -> EQ Bool
t =:= u = do
  (ctx, d) <- ask
  b <- t =?= u
  unless b $
    forM_ (substs t ctx d ++ substs u ctx d) $ \s -> liftCC $ do
      t' <- subst s t
      u' <- subst s u
      t' CC.=:= u'
  return b

type Subst = Symbol -> Int

substs :: Term -> Map TypeRep Universe -> Int -> [Subst]
substs t univ d = map lookup (sequence (map choose vars))
  where vars = map (maximumBy (comparing snd)) .
               partitionBy fst .
               holes $ t

        choose (x, n) =
          let m = Map.findWithDefault (error "NaiveEquationalReasoning.substs: empty universe")
                  (symbolType x) univ in
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
