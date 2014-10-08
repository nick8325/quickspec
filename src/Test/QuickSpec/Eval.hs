{-# LANGUAGE CPP, ConstraintKinds, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections #-}
module Test.QuickSpec.Eval where

#include "errors.h"
import Test.QuickSpec.Base
import Test.QuickSpec.Utils
import Test.QuickSpec.Type
import Test.QuickSpec.Term
import Test.QuickSpec.Signature
import Test.QuickSpec.Equation
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

type M = StateT S IO

data S = S {
  schemas       :: Schemas,
  schemaTestSet :: TestSet,
  termTestSet   :: Map (Poly Schema) TestSet,
  pruner        :: SimplePruner }

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
      pruner        = emptyPruner }

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
  ss <- gets schemas
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
  _ <- execStateT (go 1 sig ts) (initialState ts)
  return ()

go :: Int -> Signature -> TestSet -> M ()
go 10 _ _ = return ()
go n sig emptyTs = do
  modify (\s -> s { schemas = Map.insert n Map.empty (schemas s) })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  lift $ putStr ("\n\nSize " ++ show n ++ ", " ++ show (length ss) ++ " schemas to consider: ")
  mapM_ (consider sig emptyTs) ss
  go (n+1) sig emptyTs

allUnifications :: Term -> [Term]
allUnifications t = map f ss
  where
    vs = [ map (x,) xs | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = rename (go s) t

consider :: Signature -> TestSet -> Schema -> M ()
consider sig emptyTs s = do
  state <- get
  let t = instantiate s
  case evalState (repUntyped (encodeTypes t)) (pruner state) of
    Nothing -> do
      -- Need to test this term
      let skel = skeleton t
      case insert (poly skel) (schemaTestSet state) of
        Nothing ->
          accept s
        Just (Old u) -> do
          --lift (putStrLn ("Found schema equality! " ++ prettyShow (untyped skel :=: untyped u)))
          lift $ putStr "!"
          let s = schema u
              extras =
                case Map.lookup (poly s) (termTestSet state) of
                  Nothing -> allUnifications (instantiate (schema u))
                  Just _ -> []
          modify (\st -> st { termTestSet = Map.insertWith (\x y -> y) (poly s) emptyTs (termTestSet st) })
          mapM_ (considerTerm sig s) (sortBy (comparing measure) (extras ++ allUnifications t))
        Just (New ts') -> do
          lift $ putStr "O"
          modify (\st -> st { schemaTestSet = ts' })
          when (simple s) $ do
            modify (\st -> st { termTestSet = Map.insertWith (\x y -> y) (poly s) emptyTs (termTestSet st) })
            mapM_ (considerTerm sig s) (sortBy (comparing measure) (allUnifications (instantiate s)))
          accept s
    Just u | measure (schema (decodeTypes u)) < measure s -> do
      lift $ putStr "X"
      -- lift $ putStrLn ("Throwing away redundant schema: " ++ prettyShow t ++ " -> " ++ prettyShow (decodeTypes u))
      let pruner' = execState (unifyUntyped (encodeTypes t) u) (pruner state)
      put state { pruner = pruner' }

-- simple t = size t <= 5
-- simple t = True
simple t = False

considerTerm :: Signature -> Schema -> Term -> M ()
considerTerm sig s t = do
  state <- get
  case evalState (repUntyped (encodeTypes t)) (pruner state) of
    Nothing -> do
      --lift $ putStrLn ("Couldn't simplify " ++ prettyShow (t))
      case insert (poly t) (Map.findWithDefault __ (poly s) (termTestSet state)) of
        Nothing ->
          ERROR "testable term became untestable"
        Just (Old u) -> do
          found t u
          modify (\st -> st { pruner = execState (Test.QuickSpec.Pruning.unify (t :=: u)) (pruner st) })
        Just (New ts') -> do
          lift $ putStr "o"
          modify (\st -> st { termTestSet = Map.insert (poly s) ts' (termTestSet st) })
    Just u -> do
      lift $ putStr "x"
      --lift $ putStrLn ("Throwing away redundant term: " ++ prettyShow (untyped t) ++ " -> " ++ prettyShow (decodeTypes u))
      let pruner' = execState (unifyUntyped (encodeTypes t) u) (pruner state)
      put state { pruner = pruner' }

found :: Term -> Term -> M ()
found t u = do
  Simple.S eqs <- gets pruner
  case False of -- evalState (Pruning.unify (t :=: u)) (E.S eqs) of
    True -> do
      lift $ putStrLn ("\nProved by E: " ++ prettyShow t ++ " = " ++ prettyShow u)
      return ()
    False ->
      lift $ putStrLn ("\n******** " ++ prettyShow t ++ " = " ++ prettyShow u)

accept :: Schema -> M ()
accept s = do
  --lift (putStrLn ("Accepting schema " ++ prettyShow s))
  modify (\st -> st { schemas = Map.adjust f (size s) (schemas st) })
  where
    t = instantiate s
    f m = Map.insertWith (++) (poly (typ t)) [poly s] m

instance MemoTable Type where
  table = Memo.wrap f g table
    where
      f :: Either Int (TyCon, [Type]) -> Type
      f (Left x) = Var (TyVar x)
      f (Right (x, xs)) = Fun x xs
      g :: Type -> Either Int (TyCon, [Type])
      g (Var (TyVar x)) = Left x
      g (Fun x xs) = Right (x, xs)

instance MemoTable TyCon where
  table = Memo.wrap f g table
    where
      f :: Maybe T.TyCon -> TyCon
      f (Just x) = TyCon x
      f Nothing = Arrow
      g :: TyCon -> Maybe T.TyCon
      g (TyCon x) = Just x
      g Arrow = Nothing

instance MemoTable T.TyCon where
  table = Memo.wrap f g table
    where
      f :: (Word64, Word64) -> T.TyCon
      f (x, y) = T.TyCon (T.Fingerprint x y) undefined undefined undefined
      g :: T.TyCon -> (Word64, Word64)
      g (T.TyCon (T.Fingerprint x y) _ _ _) = (x, y)
