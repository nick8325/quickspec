{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections #-}
module QuickSpec.Eval where

#include "errors.h"
import QuickSpec.Base hiding (unify)
import qualified QuickSpec.Base as Base
import QuickSpec.Utils
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Signature
import QuickSpec.Prop
import Data.Map(Map)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad
import QuickSpec.Pruning hiding (createRules)
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
import Test.QuickCheck.Random
import Data.Monoid hiding ((<>))

type M = RulesT Event (StateT S (PrunerT SimplePruner IO))

data S = S {
  schemas       :: Schemas,
  schemaTestSet :: TestSet Schema,
  termTestSet   :: Map Schema (TestSet TermFrom),
  freshTestSet  :: TestSet TermFrom,
  types         :: Set Type }

data Event =
    Schema (Poly Schema) (KindOf Schema)
  | Term   TermFrom      (KindOf TermFrom)
  | ConsiderSchema (Poly Schema)
  | ConsiderTerm   TermFrom
  | Type           (Poly Type)
  | UntestableType (Poly Type)
  deriving (Eq, Ord)

instance Pretty Event where
  pretty (Schema s k) = text "schema" <+> pretty s <> text ":" <+> pretty k
  pretty (Term t k) = text "term" <+> pretty t <> text ":" <+> pretty k
  pretty (ConsiderSchema s) = text "consider schema" <+> pretty s
  pretty (ConsiderTerm t) = text "consider term" <+> pretty t
  pretty (Type ty) = text "type" <+> pretty ty
  pretty (UntestableType ty) = text "untestable type" <+> pretty ty

data KindOf a = Untestable | Representative | EqualTo a
  deriving (Eq, Ord)

instance Pretty a => Pretty (KindOf a) where
  pretty Untestable = text "untestable"
  pretty Representative = text "representative"
  pretty (EqualTo x) = text "equal to" <+> pretty x

type Schemas = Map Int (Map (Poly Type) [Poly Schema])

initialState :: Signature -> [(QCGen, Int)] -> S
initialState sig seeds =
  S { schemas       = Map.empty,
      schemaTestSet = emptyTestSet (makeTester specialise e seeds sig),
      termTestSet   = Map.empty,
      freshTestSet  = emptyTestSet (makeTester specialise e seeds sig),
      types         = typeUniverse sig }
  where
    e = table (env sig)

schemasOfSize :: Int -> Signature -> M [Schema]
schemasOfSize 1 sig =
  return $
    [Var (Hole (Var (TyVar 0)))] ++
    [Fun c [] | c <- constants sig]
schemasOfSize n _ = do
  ss <- lift $ gets schemas
  return $
    [ unPoly (apply f x)
    | i <- [1..n-1],
      let j = n-i,
      (fty, fs) <- Map.toList =<< maybeToList (Map.lookup i ss),
      canApply fty (poly (Var (TyVar 0))),
      or [ canApply f (poly (Var (Hole (Var (TyVar 0))))) | f <- fs ],
      (xty, xs) <- Map.toList =<< maybeToList (Map.lookup j ss),
      canApply fty xty,
      f <- fs,
      canApply f (poly (Var (Hole (Var (TyVar 0))))),
      x <- xs ]

quickSpecWithBackground :: Signature -> Signature -> IO [Prop]
quickSpecWithBackground sig1 sig2 = unbuffered $ do
  putStrLn "== Signature for background theory =="
  prettyPrint sig1
  putStrLn ""
  eqs <- quickSpecMain sig1

  putStrLn "== Signature (excluding background theory) =="
  prettyPrint sig2
  putStrLn ""
  let sig = sig1 `mappend` sig2
  quickSpecMain sig { background = eqs ++ background sig }

quickSpec :: Signature -> IO [Prop]
quickSpec sig = unbuffered $ do
  putStrLn "== Signature =="
  prettyPrint sig
  putStrLn ""
  quickSpecMain sig

quickSpecMain :: Signature -> IO [Prop]
quickSpecMain sig = do
  seeds <- fmap (take 1000) (genSeeds 20)
  runPruner sig (evalStateT (runRulesT (createRules sig >> go 1 sig)) (initialState sig seeds))

go :: Int -> Signature -> M [Prop]
go 10 _ = do
  es <- getEvents
  let numEvents = length es
      numSchemas  = length [ () | Schema{} <- es ]
      numTerms    = length [ () | Term{}   <- es ]
      numCreation = length [ () | ConsiderSchema{} <- es ] + length [ () | ConsiderTerm{} <- es ]
      numMisc = numEvents - numSchemas - numTerms - numCreation
  h <- numHooks
  Simple.S eqs <- lift (lift (liftPruner get))
  liftIO $ putStrLn (show numEvents ++ " events created in total (" ++
                     show numSchemas ++ " schemas, " ++
                     show numTerms ++ " terms, " ++
                     show numCreation ++ " creation, " ++
                     show numMisc ++ " miscellaneous).")
  liftIO $ putStrLn (show (length eqs) ++ " equations in background theory, " ++
                     show h ++ " hooks installed.\n")
  return (map (fmap fromPruningTerm) eqs)

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
    vs = [ map (x,) xs | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = rename (go s) t

createRules :: Signature -> M ()
createRules sig = do
  rule $ do
    Schema s k <- event
    execute $ do
      accept s
      let ms = oneTypeVar (unPoly s)
      case k of
        Untestable -> return ()
        EqualTo t -> do
          considerRenamings t t
          considerRenamings t ms
        Representative -> do
          when (size ms <= 5) $
            considerRenamings ms ms

  rule $ do
    Term (From s t) k <- event
    execute $
      case k of
        Untestable ->
          ERROR ("Untestable instance " ++ prettyShow t ++ " of testable schema " ++ prettyShow s)
        EqualTo (From _ u) -> found sig t u
        Representative -> return ()

  rule $ do
    ConsiderSchema s <- event
    types <- execute $ lift $ gets types
    require (and [ oneTypeVar (typ t) `Set.member` types | t <- subterms (unPoly s) ])
    execute (consider (Schema s) (unPoly (oneTypeVar s)))

  rule $ do
    ConsiderTerm t@(From _ t') <- event
    execute (consider (Term t) t)

  rule $ do
    Schema s _ <- event
    execute $
      generate (Type (polyTyp s))

  rule $ do
    Type ty1 <- event
    Type ty2 <- event
    require (ty1 < ty2)
    Just mgu <- return (polyMgu ty1 ty2)
    let tys = [ty1, ty2] \\ [mgu]

    Schema s Representative <- event
    require (polyTyp s `elem` tys)

    execute $
      generate (ConsiderSchema (fromMaybe __ (cast (unPoly mgu) s)))

  rule $ do
    Schema s Untestable <- event
    require (arity (typ s) == 0)
    execute $
      generate (UntestableType (polyTyp s))

  rule $ do
    UntestableType ty <- event
    execute $
      liftIO $ putStrLn $
        "Warning: generated term of untestable type " ++ prettyShow ty

  -- rule $ event >>= execute . liftIO . prettyPrint

considerRenamings :: Schema -> Schema -> M ()
considerRenamings s s' = do
  sequence_ [ generate (ConsiderTerm (From s t)) | t <- ts ]
  where
    ts = sortBy (comparing measure) (allUnifications (instantiate s'))

class (Eq a, Typed a) => Considerable a where
  generalise :: a -> Term
  specialise :: a -> Term
  getTestSet :: a -> M (TestSet a)
  putTestSet :: a -> TestSet a -> M ()

consider :: Considerable a => (KindOf a -> Event) -> a -> M ()
consider makeEvent x = do
  types  <- lift $ gets types
  let t = generalise x
  res <- lift (lift (rep t))
  case res of
    Just u | measure u < measure t ->
      lift (lift (axiom ([] :=>: t :=: u)))
    _ -> do
      ts <- getTestSet x
      case insert x ts of
        Nothing ->
          generate (makeEvent Untestable)
        Just (Old y) ->
          generate (makeEvent (EqualTo y))
        Just (New ts) -> do
          putTestSet x ts
          generate (makeEvent Representative)

instance Considerable Schema where
  generalise = instantiate . oneTypeVar
  specialise = skeleton . generalise
  getTestSet _ = lift $ gets schemaTestSet
  putTestSet _ ts = lift $ modify (\s -> s { schemaTestSet = ts })

data TermFrom = From Schema Term deriving (Eq, Ord, Show)

instance Pretty TermFrom where
  pretty (From s t) = pretty t <+> text "from" <+> pretty s

instance Typed TermFrom where
  typ (From _ t) = typ t
  typeSubstA f (From s t) = From s <$> typeSubstA f t

instance Considerable TermFrom where
  generalise (From _ t) = t
  specialise (From _ t) = t
  getTestSet (From s _) = lift $ do
    ts <- gets freshTestSet
    gets (Map.findWithDefault ts s . termTestSet)
  putTestSet (From s _) ts =
    lift $ modify (\st -> st { termTestSet = Map.insert s ts (termTestSet st) })

found :: Signature -> Term -> Term -> M ()
found sig t u = do
  let prop = [] :=>: t :=: u
  Simple.S eqs <- lift (lift (liftPruner get))
  types <- lift $ gets types
  lift (lift (axiom prop))
  res <- liftIO $ E.eUnify eqs (toGoal prop)
  case res of
    True ->
      return ()
    False -> do
      liftIO $ putStrLn (prettyShow (prettyRename sig prop))

accept :: Poly Schema -> M ()
accept s = do
  lift $ modify (\st -> st { schemas = Map.adjust f (size (unPoly s)) (schemas st) })
  where
    f m = Map.insertWith (++) (polyTyp s) [s] m
