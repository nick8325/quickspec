{-# LANGUAGE CPP, ConstraintKinds, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections #-}
module Test.QuickSpec.Eval where

#include "errors.h"
import Test.QuickSpec.Base
import Test.QuickSpec.Utils
import Test.QuickSpec.Type
import Test.QuickSpec.Term
import Test.QuickSpec.TestTree
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
import Data.MemoCombinators
import Data.MemoCombinators.Class
import Test.QuickCheck hiding (collect, Result)
import System.Random
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import qualified Data.Typeable.Internal as T
import Data.Word
import Debug.Trace
import System.IO

type TestSet = Map Type (Value TestedTerms)

data TestedTerms a =
  TestedTerms {
    dict :: Dict (Ord a),
    testedTerms :: [TestedTerm a] }

data TestedTerm a =
  TestedTerm {
    term  :: Term,
    tests :: [a] }

type M = StateT S IO

data S = S {
  schemas       :: Schemas,
  schemaTestSet :: TestSet,
  termTestSet   :: Map Schema TestSet,
  pruner        :: SimplePruner }

initialTestedTerms :: Signature -> Type -> Maybe (Value TestedTerms)
initialTestedTerms sig ty = do
  Instance dict <- findInstance ty (ords sig)
  return . toValue $
    TestedTerms {
      dict = dict,
      testedTerms = [] }

findTestSet :: Signature -> Type -> TestSet -> Maybe (Value TestedTerms)
findTestSet sig ty m =
  Map.lookup (normaliseType ty) m `mplus`
  initialTestedTerms sig ty

data Result = New TestSet | Old Term | Untestable

insert :: Signature -> Value TestedTerm -> TestSet -> Result
insert sig x ts =
  case findTestSet sig (typ x) ts of
    Nothing -> Untestable
    Just tts ->
      let r = fromMaybe __ (pairValues insert1 x tts) in
      case ofValue isNew1 r of
        True ->
          New (Map.insert (normaliseType (typ x)) (mapValue (\(New1 tts) -> tts) r) ts)
        False ->
          Old (ofValue (\(Old1 t) -> t) r)

data Result1 a = New1 (TestedTerms a) | Old1 Term
isNew1 (New1 _) = True
isNew1 _ = False

insert1 :: TestedTerm a -> TestedTerms a -> Result1 a
insert1 x ts =
  case dict ts of
    Dict -> aux ts' (tests x) (testedTerms ts)
  where
    ts' = ts { testedTerms = x:testedTerms ts }
    aux :: Ord a => TestedTerms a -> [a] -> [TestedTerm a] -> Result1 a
    aux x _ [] = New1 x
    aux y (x:xs) ts =
      aux y xs [ t { tests = tail (tests t) }
               | t <- ts,
                 head (tests t) == x ]
    aux _ [] [t] = Old1 (term t)
    aux _ [] _ = ERROR "two equal terms in TestedTerm structure"

makeTests :: (Type -> Value Gen) -> [(QCGen, Int)] -> Term -> Value TestedTerm
makeTests env tests t =
  mapValue (TestedTerm t . f) (evaluateTerm env t)
  where
    f :: Gen a -> [a]
    f x = map (uncurry (unGen x)) tests

env :: Signature -> Type -> Value Gen
env sig ty =
  case findInstance ty (arbs sig) of
    Nothing ->
      toValue (ERROR $ "missing arbitrary instance for " ++ prettyShow ty :: Gen A)
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

collect :: Typed a => [a] -> Map Type [a]
collect xs =
  Map.fromList [(typ y, ys) | ys@(y:_) <- partitionBy typ xs]

schemasOfSize :: Int -> Signature -> M [Schema]
schemasOfSize 1 sig =
  return (Var (Var (TyVar 0)):[Fun c [] | c <- constants sig])
schemasOfSize n _ = do
  ss <- gets schemas
  return $
    [ apply f x
    | i <- [1..n-1],
      let j = n-i,
      (fty, fs) <- Map.toList =<< maybeToList (Map.lookup i ss),
      canApply fty (Var (TyVar 0)),
      or [ canApply f (Var (Var (TyVar 0))) | f <- fs ],
      (xty, xs) <- Map.toList =<< maybeToList (Map.lookup j ss),
      canApply fty xty,
      f <- fs,
      canApply f (Var (Var (TyVar 0))),
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
  _ <- execStateT (go 1 sig (take 100 seeds) (table (env sig))) initialState
  return ()

go :: Int -> Signature -> [(QCGen, Int)] -> (Type -> Value Gen) -> M ()
go 12 _ _ _ = return ()
go n sig seeds gen = do
  modify (\s -> s { schemas = Map.insert n Map.empty (schemas s) })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  lift $ putStr ("\n\nSize " ++ show n ++ ", " ++ show (length ss) ++ " schemas to consider: ")
  mapM_ (consider sig seeds gen) ss
  go (n+1) sig seeds gen

allUnifications :: Term -> [Term]
allUnifications t = map f ss
  where
    vs = [ map (x,) xs | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = rename (go s) t

consider :: Signature -> [(QCGen, Int)] -> (Type -> Value Gen) -> Schema -> M ()
consider sig gen env s = do
  state <- get
  let t = instantiate s
  case evalState (repUntyped (encodeTypes t)) (pruner state) of
    Nothing -> do
      -- Need to test this term
      let skel = skeleton t
      case insert sig (makeTests env gen skel) (schemaTestSet state) of
        Untestable ->
          accept s
        Old u -> do
          --lift (putStrLn ("Found schema equality! " ++ prettyShow (untyped skel :=: untyped u)))
          lift $ putStr "!"
          let s = schema u
              extras =
                case Map.lookup (normaliseType s) (termTestSet state) of
                  Nothing -> allUnifications (instantiate (schema u))
                  Just _ -> []
          modify (\st -> st { termTestSet = Map.insertWith (\x y -> y) (normaliseType s) Map.empty (termTestSet st) })
          mapM_ (considerTerm sig gen env s) (sortBy (comparing measure) (extras ++ allUnifications t))
        New ts' -> do
          lift $ putStr "O"
          modify (\st -> st { schemaTestSet = ts' })
          when (simple s) $ do
            modify (\st -> st { termTestSet = Map.insertWith (\x y -> y) (normaliseType s) Map.empty (termTestSet st) })
            mapM_ (considerTerm sig gen env s) (sortBy (comparing measure) (allUnifications (instantiate s)))
          accept s
    Just u -> do
      lift $ putStr "X"
      --lift $ putStrLn ("Throwing away redundant schema: " ++ prettyShow (untyped t) ++ " -> " ++ prettyShow (decodeTypes u))
      let pruner' = execState (unifyUntyped (encodeTypes t) u) (pruner state)
      put state { pruner = pruner' }

simple t = size t <= 3

considerTerm :: Signature -> [(QCGen, Int)] -> (Type -> Value Gen) -> Schema -> Term -> M ()
considerTerm sig gen env s t = do
  state <- get
  case evalState (repUntyped (encodeTypes t)) (pruner state) of
    Nothing -> do
      --lift $ putStrLn ("Couldn't simplify " ++ prettyShow (t))
      case insert sig (makeTests env gen t) (Map.findWithDefault __ (normaliseType s) (termTestSet state)) of
        Untestable ->
          ERROR "testable term became untestable"
        Old u -> do
          found t u
          modify (\st -> st { pruner = execState (Test.QuickSpec.Pruning.unify (t :=: u)) (pruner st) })
        New ts' -> do
          lift $ putStr "o"
          modify (\st -> st { termTestSet = Map.insert (normaliseType s) ts' (termTestSet st) })
    Just u -> do
      lift $ putStr "x"
      --lift $ putStrLn ("Throwing away redundant term: " ++ prettyShow (untyped t) ++ " -> " ++ prettyShow (decodeTypes u))
      let pruner' = execState (unifyUntyped (encodeTypes t) u) (pruner state)
      put state { pruner = pruner' }

found :: Term -> Term -> M ()
found t u = do
  Simple.S eqs <- gets pruner
  case evalState (Pruning.unify (t :=: u)) (E.S eqs) of
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
    f m = Map.insertWith (++) (normaliseType (typ t)) [s] m

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
