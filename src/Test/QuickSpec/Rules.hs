{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Test.QuickSpec.Rules(
  RulesT, runRulesT,
  on, onMatch, signal, numEvents, numHooks) where

import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Applicative

newtype RulesT e m a =
  RulesT {
    unRulesT :: StateT (S e m) m a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (RulesT e) where
  lift m = RulesT (lift m)

data S e m =
  S {
    events :: Map e (Event e m),
    hooks  :: [e -> RulesT e m ()] }

data Event e m =
    Fired
  | Waiting [RulesT e m ()]

runRulesT :: Monad m => RulesT e m a -> m a
runRulesT m = evalStateT (unRulesT m) (S Map.empty [])

numEvents :: Monad m => RulesT e m Int
numEvents =
  RulesT $ do
    es <- gets events
    return (length [ () | Fired <- Map.elems es ])

numHooks :: Monad m => RulesT e m Int
numHooks = RulesT (gets (length . hooks))

on :: (Monad m, Ord e) => e -> RulesT e m () -> RulesT e m ()
on e m =
  RulesT $ do
    es <- gets events
    case Map.findWithDefault (Waiting []) e es of
      Fired ->
        unRulesT m
      Waiting ms ->
        modify (\s -> s { events = Map.insert e (Waiting (m:ms)) (events s) })

onMatch :: (Monad m, Ord e) => (e -> RulesT e m ()) -> RulesT e m ()
onMatch f =
  RulesT $ do
    modify (\s -> s { hooks = f:hooks s })
    es <- gets events
    let fired = [ e | (e, Fired) <- Map.toList es ]
    unRulesT (mapM_ f fired)

signal :: (Monad m, Ord e) => e -> RulesT e m ()
signal e =
  RulesT $ do
    es <- gets events
    case Map.findWithDefault (Waiting []) e es of
      Fired ->
        return ()
      Waiting ms -> do
        modify (\s -> s { events = Map.insert e Fired (events s) })
        hs <- gets hooks
        unRulesT $ do
          sequence_ [ h e | h <- hs ]
          sequence_ ms
