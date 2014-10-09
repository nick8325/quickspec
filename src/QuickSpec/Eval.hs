{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections #-}
module QuickSpec.Eval where

#include "errors.h"
import QuickSpec.Base hiding (unify)
import qualified QuickSpec.Base as Base
import QuickSpec.Utils
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Signature
import QuickSpec.Equation
import Data.Map(Map)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad
import QuickSpec.Pruning
import QuickSpec.Pruning.Simple hiding (S)
import qualified QuickSpec.Pruning.Simple as Simple
import qualified QuickSpec.Pruning.E as E
import Data.List hiding (insert)
import Data.Ord
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Data.MemoCombinators.Class
import QuickSpec.TestSet
import QuickSpec.Rules
import Control.Monad.IO.Class
import QuickSpec.Memo()
import Control.Applicative
import QuickSpec.Test

type M = RulesT Event (StateT S IO)

data S = S {
  schemas       :: Schemas,
  schemaTestSet :: TestSet (Poly Schema),
  termTestSet   :: Map (Poly Schema) (TestSet TermFrom),
  pruner        :: SimplePruner,
  freshTestSet  :: TestSet TermFrom }

data Event =
    Schema (Poly Schema)   (KindOf (Poly Schema))
  | Term   TermFrom        (KindOf TermFrom)
  | ConsiderSchema (Poly Schema)
  | ConsiderTerm   TermFrom
  | Type           (Poly Type)
  | UntestableType (Poly Type)
  deriving (Eq, Ord, Show)

data KindOf a = Untestable | Representative | EqualTo a
  deriving (Eq, Ord, Show)

type Schemas = Map Int (Map (Poly Type) [Poly Schema])

initialState :: TestSet (Poly Schema) -> TestSet TermFrom -> S
initialState ts ts' =
  S { schemas       = Map.empty,
      schemaTestSet = ts,
      termTestSet   = Map.empty,
      pruner        = emptyPruner,
      freshTestSet  = ts' }

schemasOfSize :: Int -> Signature -> M [Schema]
schemasOfSize 1 sig =
  return $
    [Var (Var (TyVar 0))] ++
    [Fun c [] | c <- constants sig]
schemasOfSize n _ = do
  ss <- lift $ gets schemas
  return $
    [ mono (apply f x)
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
      ts = emptyTestSet (makeTester (skeleton . instantiate . mono) e seeds sig)
      ts' = emptyTestSet (makeTester (\(From _ t) -> t) e seeds sig)
  _ <- execStateT (runRulesT (createRules sig >> go 1 sig)) (initialState ts ts')
  return ()

go :: Int -> Signature -> M ()
go 10 _ = do
  es <- getEvents
  let isSchema (Schema _ _) = True
      isSchema _ = False
      isTerm (Term _ _) = True
      isTerm _ = False
      isCreation (ConsiderSchema _) = True
      isCreation (ConsiderTerm _) = True
      isCreation _ = False
      numEvents = length es
      numSchemas = length (filter isSchema es)
      numTerms = length (filter isTerm es)
      numCreation = length (filter isCreation es)
      numMisc = numEvents - numSchemas - numTerms - numCreation
  h <- numHooks
  liftIO $ putStrLn (show numEvents ++ " events created in total (" ++
                     show numSchemas ++ " schemas, " ++
                     show numTerms ++ " terms, " ++
                     show numCreation ++ " creation, " ++
                     show numMisc ++ " miscellaneous).")
  liftIO $ putStrLn (show h ++ " hooks installed.")
go n sig = do
  lift $ modify (\s -> s { schemas = Map.insert n Map.empty (schemas s) })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  liftIO $ putStrLn ("Size " ++ show n ++ ", " ++ show (length ss) ++ " schemas to consider:")
  mapM_ (generate . ConsiderSchema . poly) ss
  liftIO $ putStrLn ""
  go (n+1) sig

allUnifications :: Term -> [Term]
allUnifications t = map f ss
  where
    vs = [ map (x,) xs | xs <- partitionBy (unifyTypeVars . typ) (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = rename (go s) t
    unifyTypeVars = typeSubst (const (Var (TyVar 0)))

createRules :: Signature -> M ()
createRules sig = do
  rule $ do
    Schema s k <- event
    execute $
      case k of
        Untestable -> accept s
        EqualTo t -> do
          considerRenamings t t
          considerRenamings t s
        Representative -> do
          accept s
          when (size (mono s) <= 5) $
            considerRenamings s s

  rule $ do
    Term (From s t) k <- event
    execute $
      case k of
        Untestable ->
          ERROR ("Untestable instance " ++ prettyShow t ++ " of testable schema " ++ prettyShow (mono s))
        EqualTo (From _ u) -> found t u
        Representative -> return ()

  let allowedTypes =
        Set.fromList (Var (TyVar 0):map (typeSubst (const (Var (TyVar 0))) . typeRes . typ) (constants sig))
  rule $ do
    ConsiderSchema s <- event
    require (typeRes (typ (skeleton (instantiate (mono s)))) `Set.member` allowedTypes)
    execute (consider s)

  rule $ do
    ConsiderTerm s <- event
    execute (consider s)

  rule $ do
    Schema s _ <- event
    execute $
      generate (Type (polyTyp s))

  rule $ do
    Type ty1 <- event
    Type ty2 <- event
    require (mono ty1 < mono ty2)
    let (ty1', ty2') = mono (polyPair ty1 ty2)
    Just sub <- return (Base.unify ty1' ty2')
    let mgu = poly (typeSubst (evalSubst sub) ty1')
        tys = [ty1, ty2] \\ [mgu]

    Schema s Representative <- event
    require (polyTyp s `elem` tys)

    execute $
      generate (ConsiderSchema (fromMaybe __ (cast (mono mgu) s)))

  rule $ do
    Schema s Untestable <- event
    require (arity (typ s) == 0)
    execute $
      generate (UntestableType (polyTyp (defaultType s)))

  rule $ do
    UntestableType ty <- event
    execute $
      liftIO $ putStrLn $
        "Warning: generated term of untestable type " ++ prettyShow ty

  -- rule $ event >>= execute . liftIO . print

considerRenamings :: Poly Schema -> Poly Schema -> M ()
considerRenamings s s' = do
  sequence_ [ generate (ConsiderTerm (From s t)) | t <- ts ]
  where
    ts = sortBy (comparing measure) (allUnifications (instantiate (mono s')))

class (Eq a, Typed a) => Considerable a where
  toTerm     :: a -> Term
  getTestSet :: a -> M (TestSet a)
  putTestSet :: a -> TestSet a -> M ()
  makeEvent  :: a -> KindOf a -> Event

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
          generate (makeEvent x Untestable)
        Just (Old y) ->
          generate (makeEvent x (EqualTo y))
        Just (New ts) -> do
          putTestSet x ts
          generate (makeEvent x Representative)

instance Considerable (Poly Schema) where
  toTerm = instantiate . mono
  getTestSet _ = lift $ gets schemaTestSet
  putTestSet _ ts = lift $ modify (\s -> s { schemaTestSet = ts })
  makeEvent = Schema

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
  makeEvent = Term

found :: Term -> Term -> M ()
found t u = do
  Simple.S eqs <- lift $ gets pruner
  lift $ modify (\s -> s { pruner = execState (unify (t :=: u)) (pruner s) })
  case False && evalState (unify (t :=: u)) (E.S eqs) of
    True ->
      return ()
    False ->
      liftIO $ putStrLn (prettyShow t ++ " = " ++ prettyShow u)

accept :: Poly Schema -> M ()
accept s = do
  lift $ modify (\st -> st { schemas = Map.adjust f (size (mono s)) (schemas st) })
  where
    f m = Map.insertWith (++) (polyTyp s) [s] m
