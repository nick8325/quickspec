{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module QuickSpec.Rules(
  RulesT, runRulesT, generate, rule,
  RuleT,  event, require, execute,
  getEvents, numHooks) where

import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Applicative
import Control.Monad

newtype RulesT e m a =
  RulesT {
    unRulesT :: StateT (S e m) m a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (RulesT e) where
  lift m = RulesT (lift m)

data S e m =
  S {
    events :: Set e,
    hooks  :: [e -> RulesT e m ()] }

runRulesT :: Monad m => RulesT e m a -> m a
runRulesT m = evalStateT (unRulesT m) (S Set.empty [])

getEvents :: Monad m => RulesT e m [e]
getEvents = RulesT (gets (Set.toList . events))

numHooks :: Monad m => RulesT e m Int
numHooks = RulesT (gets (length . hooks))

onMatch :: (Monad m, Ord e) => (e -> RulesT e m ()) -> RulesT e m ()
onMatch f =
  RulesT $ do
    modify (\s -> s { hooks = f:hooks s })
    es <- gets (Set.toList . events)
    unRulesT (mapM_ f es)

generate :: (Monad m, Ord e) => e -> RulesT e m ()
generate e =
  RulesT $ do
    es <- gets events
    case Set.member e es of
      True ->
        return ()
      False -> do
        modify (\s -> s { events = Set.insert e (events s) })
        hs <- gets hooks
        unRulesT (sequence_ [ h e | h <- hs ])

newtype RuleT e m a =
  RuleT {
    unRuleT :: (a -> RulesT e m ()) -> RulesT e m () }

instance Monad m => Functor (RuleT e m) where fmap = liftM
instance Monad m => Applicative (RuleT e m) where
  pure = return
  (<*>) = liftM2 ($)
instance Monad m => Monad (RuleT e m) where
  return x = RuleT (\k -> k x)
  m >>= f =
    RuleT $ \k ->
      unRuleT m (\x -> unRuleT (f x) k)
  fail _ = RuleT (\_ -> return ())

rule :: Monad m => RuleT e m () -> RulesT e m ()
rule m = unRuleT m (\() -> return ())

event :: (Ord e, Monad m) => RuleT e m e
event = RuleT onMatch

require :: Monad m => Bool -> RuleT e m ()
require True  = return ()
require False = fail ""

execute :: Monad m => RulesT e m a -> RuleT e m a
execute m = RuleT (\k -> m >>= k)
