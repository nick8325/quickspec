{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections #-}
module Test.QuickSpec.Eval where

#include "errors.h"
import Test.QuickSpec.Base hiding (unify)
import Test.QuickSpec.Utils
import Test.QuickSpec.Type
import Test.QuickSpec.Term
import Test.QuickSpec.Signature
import Test.QuickSpec.Equation
import Data.Map(Map)
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad
import Test.QuickSpec.Pruning
import Test.QuickSpec.Pruning.Simple hiding (S)
import qualified Test.QuickSpec.Pruning.Simple as Simple
import qualified Test.QuickSpec.Pruning.E as E
import Data.List hiding (insert)
import Data.Ord
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Data.MemoCombinators.Class
import Test.QuickSpec.TestSet
import Test.QuickSpec.Rules
import Control.Monad.IO.Class
import Test.QuickSpec.Memo()
import Control.Applicative
import Test.QuickSpec.Test

type M = RulesT Event (StateT S IO)

data S = S {
  schemas       :: Schemas,
  schemaTestSet :: TestSet Schema,
  termTestSet   :: Map (Poly Schema) (TestSet TermFrom),
  pruner        :: SimplePruner,
  freshTestSet  :: TestSet TermFrom }

data Event =
    Schema Schema   (KindOf Schema)
  | Term   TermFrom (KindOf TermFrom)
  | ConsiderSchema Schema
  | ConsiderTerm   TermFrom
  deriving (Eq, Ord, Show)

data KindOf a = Untestable | Representative | EqualTo a
  deriving (Eq, Ord, Show)

type Schemas = Map Int (Map (Poly Type) [Poly Schema])

initialState :: TestSet Schema -> TestSet TermFrom -> S
initialState ts ts' =
  S { schemas       = Map.empty,
      schemaTestSet = ts,
      termTestSet   = Map.empty,
      pruner        = emptyPruner,
      freshTestSet  = ts' }

schemasOfSize :: Int -> Signature -> M [Schema]
schemasOfSize 1 sig =
  return $
    [Var ty | ty <- tys] ++
    [Fun c [] | c <- constants sig]
  where
    tys = [typeOf (undefined :: [Int])]
    {-tys = [typeOf (undefined :: Int),
           typeOf (undefined :: [Bool]),
           typeOf (undefined :: Layout Bool)]-}
schemasOfSize n _ = do
  ss <- lift $ gets schemas
  return $
    [ unPoly (apply f x)
    | i <- [1..n-1],
      let j = n-i,
      (fty, fs) <- Map.toList =<< maybeToList (Map.lookup i ss),
      canApply fty (poly (Var (TyVar 0))),
      or [ canApply f (poly (Var (Var (TyVar 0)))) | f <- fs ],
      (xty, xs) <- Map.toList =<< maybeToList (Map.lookup j ss),
      canApply fty xty,
      f <- fs,
      canApply f (poly (Var (Var (TyVar 0)))),
      x <- xs ]

quickSpec :: Signature -> IO ()
quickSpec sig = unbuffered $ do
  seeds <- fmap (take 100) (genSeeds 20)
  let e = table (env sig)
      ts = emptyTestSet (makeTester (skeleton . instantiate) e seeds sig)
      ts' = emptyTestSet (makeTester (\(From _ t) -> t) e seeds sig)
  _ <- execStateT (runRulesT (createRules >> go 1 sig)) (initialState ts ts')
  return ()

go :: Int -> Signature -> M ()
go 10 _ = return ()
go n sig = do
  lift $ modify (\s -> s { schemas = Map.insert n Map.empty (schemas s) })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  liftIO $ putStrLn ("Size " ++ show n ++ ", " ++ show (length ss) ++ " schemas to consider:")
  mapM_ (signal . ConsiderSchema) ss
  liftIO $ putStrLn ""
  go (n+1) sig

allUnifications :: Term -> [Term]
allUnifications t = map f ss
  where
    vs = [ map (x,) xs | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = rename (go s) t

createRules :: M ()
createRules =
  onMatch $ \e -> do
    case e of
      Schema s Untestable -> accept s
      Schema s (EqualTo t) -> do
        considerRenamings t t
        considerRenamings t s
      Schema s Representative -> do
        accept s
        when (size s <= 5) $ considerRenamings s s
      Term (From s t) Untestable ->
        ERROR ("Untestable instance " ++ prettyShow t ++ " of testable schema " ++ prettyShow (unPoly s))
      Term (From _ t) (EqualTo (From _ u)) -> found t u
      Term _ Representative -> return ()
      ConsiderSchema s -> consider s
      ConsiderTerm   t -> consider t

considerRenamings :: Schema -> Schema -> M ()
considerRenamings s s' =
  sequence_ [ signal (ConsiderTerm (From (poly s) t)) | t <- ts ]
  where
    ts = sortBy (comparing measure) (allUnifications (instantiate s'))

class (Eq a, Typed a) => Considerable a where
  toTerm     :: a -> Term
  getTestSet :: a -> M (TestSet a)
  putTestSet :: a -> TestSet a -> M ()
  event      :: a -> KindOf a -> Event

consider :: Considerable a => a -> M ()
consider x = do
  pruner <- lift $ gets pruner
  let t = toTerm x
  case evalState (repUntyped (encodeTypes t)) pruner of
    Just u | measure (decodeTypes u) < measure t ->
      let mod = execState (unifyUntyped (encodeTypes t) u)
      in lift $ modify (\s -> s { pruner = mod pruner })
    Nothing -> do
      ts <- getTestSet x
      case insert (poly x) ts of
        Nothing ->
          signal (event x Untestable)
        Just (Old y) ->
          signal (event x (EqualTo y))
        Just (New ts) -> do
          putTestSet x ts
          signal (event x Representative)

instance Considerable Schema where
  toTerm = instantiate
  getTestSet _ = lift $ gets schemaTestSet
  putTestSet _ ts = lift $ modify (\s -> s { schemaTestSet = ts })
  event = Schema

data TermFrom = From (Poly Schema) Term deriving (Eq, Ord, Show)

instance Typed TermFrom where
  typ (From _ t) = typ t
  typeSubstA f (From s t) = From s <$> typeSubstA f t

instance Considerable TermFrom where
  toTerm (From _ t) = t
  getTestSet (From s _) = lift $ do
    ts <- gets freshTestSet
    gets (Map.findWithDefault ts s . termTestSet)
  putTestSet (From s _) ts =
    lift $ modify (\st -> st { termTestSet = Map.insert s ts (termTestSet st) })
  event = Term

found :: Term -> Term -> M ()
found t u = do
  Simple.S eqs <- lift $ gets pruner
  lift $ modify (\s -> s { pruner = execState (unify (t :=: u)) (pruner s) })
  case False && evalState (unify (t :=: u)) (E.S eqs) of
    True ->
      return ()
    False ->
      liftIO $ putStrLn (prettyShow t ++ " = " ++ prettyShow u)

accept :: Schema -> M ()
accept s = do
  lift $ modify (\st -> st { schemas = Map.adjust f (size s) (schemas st) })
  where
    f m = Map.insertWith (++) (polyTyp (poly s)) [poly s] m
