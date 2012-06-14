{-# LANGUAGE Rank2Types, TupleSections #-}
module NaiveEquationalReasoning where

import Term
import CongruenceClosure(CC)
import qualified CongruenceClosure as CC
import Data.Function
import Data.Map(Map)
import qualified Data.Map as Map
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Utils
import Typed
import Data.Ord
import Data.List
import Debug.Trace

data Context = Context {
  rel :: CC.S,
  universe :: TypeMap Universe,
  maxDepth :: Int
  }

type Universe = K (IntMap [Int])

type EQ = ReaderT (TypeMap Universe, Int) CC

initial :: Int -> [Some Term] -> Context
initial d ts =
  let n = 1+maximum (0:concatMap (some indices) ts)
      (universe, rel) =
        CC.runCC (CC.initial n) $
          forM (classify ts) $
          mapSomeM $ \(C xs) -> createUniverse xs
      
  in Context rel (Typed.fromList universe) d

createUniverse :: [Term a] -> CC (Universe a)
createUniverse ts = fmap (K . IntMap.fromList) (mapM createTerms tss)
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

(=?=) :: Term a -> Term a -> EQ Bool
t =?= u = liftCC $ do
  x <- flatten t
  y <- flatten u
  x CC.=?= y

(=:=) :: Term a -> Term a -> EQ Bool
t =:= u = do
  (ctx, d) <- ask
  b <- t =?= u
  unless b $
    forM_ (substs t ctx d ++ substs u ctx d) $ \s -> liftCC $ do
      t' <- subst s t
      u' <- subst s u
      t' CC.=:= u'
  return b

newtype Subst = Subst (forall a. Var a -> Int)

substs :: Term a -> TypeMap Universe -> Int -> [Subst]
substs t univ d = map apply (map lookup (sequence (map choose (dump vars))))
  where vars :: [(Name, Int)]
        vars = map (maximumBy (comparing snd)) .
               partitionBy fst .
               holes $ t
               
        dump xs = traceShow (t, xs) xs
        
        choose :: (Name, Int) -> [(Name, Int)]
        choose (x, n) =
          case Map.findWithDefault (error "NaiveEquationalReasoning.substs: empty universe")
               (typ_ x) univ of
            Some (K m) ->
              [ (x, t)
              | d' <- [0..d-n],
                t <- IntMap.findWithDefault [] d' m ]
        
        lookup :: [(Name, Int)] -> (Name -> Int)
        lookup ss =
          let m = IntMap.fromList [ (index x, y) | (x, y) <- ss ]
          in \x -> IntMap.findWithDefault (index x) (index x) m

        apply :: (Name -> Int) -> Subst
        apply s = Subst $ \x -> s (erase x)

subst :: Subst -> Term a -> CC Int
subst (Subst s) (Var x) = return (s x)
subst s (Const x) = return (index x)
subst s (App f x) = do
  f' <- subst s f
  x' <- subst s x
  f' CC.$$ x'

flatten :: Term a -> CC Int
flatten = subst (Subst index)
