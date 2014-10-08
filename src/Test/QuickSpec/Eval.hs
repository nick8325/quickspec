{-# LANGUAGE CPP, ConstraintKinds, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections #-}
module Test.QuickSpec.Eval where

#include "errors.h"
import Test.QuickSpec.Base hiding (unify)
import Test.QuickSpec.Utils
import Test.QuickSpec.Type
import Test.QuickSpec.Term
import Test.QuickSpec.Signature
import Test.QuickSpec.Equation
import Test.QuickSpec.Memo
import Data.Constraint
import Data.Map(Map)
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad
import Test.QuickSpec.Pruning
import qualified Test.QuickSpec.Pruning as Pruning
import Test.QuickSpec.Pruning.Simple hiding (S)
import Test.QuickSpec.Pruning.E hiding (S)
import qualified Test.QuickSpec.Pruning.Simple as Simple
import qualified Test.QuickSpec.Pruning.E as E
import Data.List hiding (insert)
import Data.Ord
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Data.MemoCombinators hiding (wrap)
import qualified Data.MemoCombinators as Memo
import Data.MemoCombinators.Class
import Test.QuickCheck hiding (collect, Result)
import System.Random
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import qualified Data.Typeable.Internal as T
import Data.Word
import Debug.Trace
import System.IO
import PrettyPrinting
import Test.QuickSpec.TestSet
import Test.QuickSpec.Rules
import Control.Monad.IO.Class

type M = RulesT Event (StateT S IO)

data S = S {
  schemas       :: Schemas,
  schemaTestSet :: TestSet,
  termTestSet   :: Map (Poly Schema) TestSet,
  pruner        :: SimplePruner,
  freshTestSet  :: TestSet }

data Event =
    Schema (EventFor Schema)
  | Term (Poly Schema) (EventFor Term)
  deriving (Eq, Ord, Show)

data EventFor a =
    Exists a
  | Untestable a
  | Equal a a
  | Representative a
  deriving (Eq, Ord, Show)

makeTester :: (Type -> Value Gen) -> [(QCGen, Int)] -> Signature -> Type -> Maybe (Value TestedTerms)
makeTester env tests sig ty = do
  Instance Dict `In` w <-
    fmap unwrap (listToMaybe [ i | i <- ords sig, typ i == ty ])
  return . wrap w $
    emptyTestedTerms (Just . reunwrap w . makeTests env tests)

makeTests :: (Type -> Value Gen) -> [(QCGen, Int)] -> Term -> Value []
makeTests env tests t =
  mapValue f (evaluateTerm env t)
  where
    f :: Gen a -> [a]
    f x = map (uncurry (unGen x)) tests

env :: Signature -> Type -> Value Gen
env sig ty =
  case [ i | i <- arbs sig, typ i == ty ] of
    [] ->
      toValue (ERROR $ "missing arbitrary instance for " ++ prettyShow ty :: Gen A)
    (i:_) ->
      forValue i $ \(Instance Dict) -> arbitrary

type Schemas = Map Int (Map (Poly Type) [Poly Schema])

instance Pruner S where
  emptyPruner      = __
  unifyUntyped t u = inPruner (unifyUntyped t u)
  repUntyped t     = inPruner (repUntyped t)

inPruner x = do
  s <- get
  let (y, s') = runState x (pruner s)
  put s { pruner = s' }
  return y

initialState :: TestSet -> S
initialState ts =
  S { schemas       = Map.empty,
      schemaTestSet = ts,
      termTestSet   = Map.empty,
      pruner        = emptyPruner,
      freshTestSet  = ts }

typeSchemas :: [Schema] -> Map Type [Schema]
typeSchemas = fmap (map schema) . collect . map instantiate

collect :: Typed a => [a] -> Map Type [a]
collect xs =
  Map.fromList [(typ y, ys) | ys@(y:_) <- partitionBy typ xs]

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

genSeeds :: Int -> IO [(QCGen, Int)]
genSeeds maxSize = do
  rnd <- newQCGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..maxSize])))

quickSpec :: Signature -> IO ()
quickSpec sig = do
  hSetBuffering stdout NoBuffering
  seeds <- genSeeds 20
  let ts = emptyTestSet (makeTester (table (env sig)) (take 100 seeds) sig)
  _ <- execStateT (runRulesT (createRules sig ts >> go 1 sig ts)) (initialState ts)
  return ()

go :: Int -> Signature -> TestSet -> M ()
go 10 _ _ = return ()
go n sig emptyTs = do
  lift $ modify (\s -> s { schemas = Map.insert n Map.empty (schemas s) })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  liftIO $ putStrLn ("Size " ++ show n ++ ", " ++ show (length ss) ++ " schemas to consider:")
  sequence_ [ signal (Schema (Exists s)) | s <- ss ]
  liftIO $ putStrLn ""
  go (n+1) sig emptyTs

allUnifications :: Term -> [Term]
allUnifications t = map f ss
  where
    vs = [ map (x,) xs | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = rename (go s) t

createRules :: Signature -> TestSet -> M ()
createRules sig ts =
  onMatch $ \e -> do
    case e of
      Schema (Exists s) -> considerSchema s
      Schema (Untestable s) -> accept s
      Schema (Equal s t) -> do
        considerRenamings t t
        considerRenamings t s
      Schema (Representative s) -> do
        accept s
        when (size s <= 5) $ considerRenamings s s
      Term s (Exists t) -> considerTerm s t
      Term s (Untestable t) ->
        ERROR ("Untestable instance " ++ prettyShow t ++ " of testable schema " ++ prettyShow s)
      Term _ (Equal t u) -> found t u
      Term _ (Representative _) -> return ()

considerRenamings s s' =
  sequence_ [ signal (Term (poly s) (Exists t)) | t <- ts ]
  where
    ts = sortBy (comparing measure) (allUnifications (instantiate s'))

data Consideration a b =
  Consideration {
    pruningTerm :: a -> Term,
    pruningMeasure :: Term -> b,
    testingTerm :: a -> Term,
    testingUnTerm :: Term -> a,
    getTestSet :: M TestSet,
    putTestSet :: TestSet -> M (),
    event :: EventFor a -> Event }

consider :: Ord b => Consideration a b -> a -> M ()
consider con x = do
  pruner <- lift $ gets pruner
  let t = pruningTerm con x
  case evalState (repUntyped (encodeTypes t)) pruner of
    Just u | pruningMeasure con (decodeTypes u) < pruningMeasure con t ->
      let mod = execState (unifyUntyped (encodeTypes t) u)
      in lift $ modify (\s -> s { pruner = mod pruner })
    Nothing -> do
      ts <- getTestSet con
      let t = testingTerm con x
      case insert (poly t) ts of
        Nothing ->
          signal (event con (Untestable x))
        Just (Old u) ->
          signal (event con (Equal x (testingUnTerm con u)))
        Just (New ts) -> do
          putTestSet con ts
          signal (event con (Representative x))

considerSchema s = consider con s
  where
    con =
      Consideration {
        pruningTerm = instantiate,
        pruningMeasure = measure . schema,
        testingTerm = skeleton . instantiate,
        testingUnTerm = schema,
        getTestSet = lift $ gets schemaTestSet,
        putTestSet = \ts -> lift $ modify (\s -> s { schemaTestSet = ts }),
        event = Schema }

considerTerm s t = consider con t
  where
    con =
      Consideration {
        pruningTerm = id,
        pruningMeasure = measure,
        testingTerm = id,
        testingUnTerm = id,
        getTestSet = getTestSet,
        putTestSet = \ts -> lift $ modify (\st -> st { termTestSet = Map.insert s ts (termTestSet st) }),
        event = Term s }
    getTestSet = lift $ do
      ts <- gets freshTestSet
      gets (Map.findWithDefault ts s . termTestSet)

found :: Term -> Term -> M ()
found t u = do
  Simple.S eqs <- lift $ gets pruner
  lift $ modify (\s -> s { pruner = execState (unify (t :=: u)) (pruner s) })
  case False of -- evalState (Pruning.unify (t :=: u)) (E.S eqs) of
    True ->
      return ()
    False ->
      liftIO $ putStrLn (prettyShow t ++ " = " ++ prettyShow u)

accept :: Schema -> M ()
accept s = do
  lift $ modify (\st -> st { schemas = Map.adjust f (size s) (schemas st) })
  where
    f m = Map.insertWith (++) (polyTyp (poly s)) [poly s] m
