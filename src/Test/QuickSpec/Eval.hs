{-# LANGUAGE CPP, ConstraintKinds, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
module Test.QuickSpec.Eval where

#include "errors.h"
import Test.QuickSpec.Base
import Test.QuickSpec.Utils
import Test.QuickSpec.Type
import Test.QuickSpec.Term
import Test.QuickSpec.TestTree
import Test.QuickSpec.Signature
import Data.Constraint
import Data.Map(Map)
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad
import Test.QuickSpec.Pruning
import Test.QuickSpec.Pruning.Simple hiding (S)
import Data.List
import Data.Ord
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Data.MemoCombinators
import Data.MemoCombinators.Class
import Test.QuickCheck hiding (collect)
import System.Random
import Test.QuickCheck.Random
import qualified Data.Typeable.Internal as T
import Data.Word
import Debug.Trace

type TestSet = Map (Typed ()) (Value TestedTerms)

data TestedTerms a =
  TestedTerms {
    dict :: Dict (Ord a),
    testedTerms :: [TestedTerm a] }

data TestedTerm a =
  TestedTerm {
    term  :: Typed Term,
    tests :: [a] }

type M = StateT S IO

data S = S {
  schemas       :: Schemas,
  schemaTestSet :: TestSet,
  termTestSet   :: TestSet,
  pruner        :: SimplePruner }

initialTestedTerms :: Signature -> Type -> Maybe (Value TestedTerms)
initialTestedTerms sig ty = do
  Instance dict <- findInstance ty (ords sig)
  return . toValue $ TestedTerms {
    dict = dict,
    testedTerms = [] }

findTestSet :: Signature -> Typed a -> TestSet -> Maybe (Value TestedTerms)
findTestSet sig ty m =
  Map.lookup (fmap (const ()) ty) m `mplus`
  initialTestedTerms sig (typ ty)

env :: Signature -> Type -> Value Gen
env sig ty =
  case findInstance ty (arbs sig) of
    Nothing ->
      ERROR $ "missing arbitrary instance for " ++ prettyShow ty
    Just (Instance (Dict :: Dict (Arbitrary a))) ->
      toValue (arbitrary :: Gen a)

type Schemas = Map Int (Map Type [Schema])

instance Pruner S where
  emptyPruner      = initialState
  unifyUntyped t u = inPruner (unifyUntyped t u)
  repUntyped t     = inPruner (repUntyped t)

inPruner x = do
  s <- get
  let (y, s') = runState x (pruner s)
  put s { pruner = s' }
  return y

initialState :: S
initialState =
  S { schemas       = Map.empty,
      schemaTestSet = Map.empty,
      termTestSet   = Map.empty,
      pruner        = emptyPruner }

typeSchemas :: [Schema] -> Map Type [Schema]
typeSchemas = fmap (map schema) . collect . map instantiate

collect :: [Typed a] -> Map Type [a]
collect xs =
  Map.fromList [(typ y, map untyped ys) | ys@(y:_) <- partitionBy typ xs]

schemasOfSize :: Int -> Signature -> M [Schema]
schemasOfSize 1 sig =
  return (Var ():[Fun c [] | c <- constants sig])
schemasOfSize n _ = do
  ss <- gets schemas
  return $
    [ apply f x
    | i <- [1..n-1],
      let j = n-i,
      (fty, fs) <- Map.toList =<< maybeToList (Map.lookup i ss),
      canApply fty (Var (TyVar 0)),
      or [ canApply f (Var ()) | f <- fs ],
      (xty, xs) <- Map.toList =<< maybeToList (Map.lookup j ss),
      canApply fty xty,
      f <- fs,
      canApply f (Var ()),
      x <- xs ]

genSeeds :: Int -> IO [(QCGen, Int)]
genSeeds maxSize = do
  rnd <- newQCGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..maxSize])))

quickSpec :: Signature -> IO ()
quickSpec sig = do
  seeds <- genSeeds 20
  _ <- execStateT (go 1 sig seeds (table (env sig))) initialState
  return ()

go :: Int -> Signature -> [(QCGen, Int)] -> (Type -> Value Gen) -> M ()
go n sig seeds gen = do
  modify (\s -> s { schemas = Map.insert n Map.empty (schemas s) })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  lift $ putStrLn ("Size " ++ show n ++ ", " ++ show (length ss) ++ " schemas to consider")
  mapM_ (consider seeds gen) ss
  mapM_ accept ss
  go (n+1) sig seeds gen

consider :: [(QCGen, Int)] -> (Type -> Value Gen) -> Schema -> M ()
consider gen s = do
  state <- get
  let t = instantiate s
  case evalState (repUntyped (encodeTypes t)) (pruner state) of
    Nothing -> do
      -- Need to test this term
      let skel = skeleton (instantiate s)

          t = evaluateTerm gen skel
      case findEval sig skel (eqRel state) of
        Nothing ->
          -- An untestable type
          accept s
        Just ev -> do
          accept s
    Just u -> do
      lift $ putStrLn ("Throwing away redundant term: " ++ prettyShow t ++ " -> " ++ prettyShow (decodeTypes u))
      let pruner' = execState (unifyUntyped (encodeTypes t) u) (pruner state)
      put state { pruner = pruner' }

accept :: Schema -> M ()
accept s = do
  lift (putStrLn ("Accepting schema " ++ prettyShow s))
  modify (\st -> st { schemas = Map.adjust f (size s) (schemas st) })
  where
    t = instantiate s
    f m = Map.insertWith (++) (typ t) [s] m

instance MemoTable Type where
  table = wrap f g table
    where
      f :: Either Int (TyCon, [Type]) -> Type
      f (Left x) = Var (TyVar x)
      f (Right (x, xs)) = Fun x xs
      g :: Type -> Either Int (TyCon, [Type])
      g (Var (TyVar x)) = Left x
      g (Fun x xs) = Right (x, xs)

instance MemoTable TyCon where
  table = wrap f g table
    where
      f :: Maybe T.TyCon -> TyCon
      f (Just x) = TyCon x
      f Nothing = Arrow
      g :: TyCon -> Maybe T.TyCon
      g (TyCon x) = Just x
      g Arrow = Nothing

instance MemoTable T.TyCon where
  table = wrap f g table
    where
      f :: (Word64, Word64) -> T.TyCon
      f (x, y) = T.TyCon (T.Fingerprint x y) undefined undefined undefined
      g :: T.TyCon -> (Word64, Word64)
      g (T.TyCon (T.Fingerprint x y) _ _ _) = (x, y)
