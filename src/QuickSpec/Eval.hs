{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections #-}
module QuickSpec.Eval where

#include "errors.h"
import QuickSpec.Base hiding (unify, terms)

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.List hiding (insert)
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Maybe
import Data.MemoUgly
import Data.Monoid hiding ((<>))
import Data.Ord
import qualified Data.Set as Set
import Data.Set(Set)
import QuickSpec.Prop
import QuickSpec.Pruning hiding (createRules, instances)
import QuickSpec.Pruning.Completion hiding (initialState)
import QuickSpec.Pruning.Simple(SimplePruner)
import qualified QuickSpec.Pruning.E as E
import qualified QuickSpec.Pruning.Z3 as Z3
import QuickSpec.Rules
import QuickSpec.Signature
import QuickSpec.Term
import QuickSpec.Test
import QuickSpec.TestSet
import QuickSpec.Type
import QuickSpec.Utils
import Test.QuickCheck.Random
import Data.Rewriting.Rule(Rule(Rule))

type M = RulesT Event (StateT S (PrunerM Completion))

data S = S {
  schemas       :: Schemas,
  terms         :: Set Term,
  schemaTestSet :: TestSet Schema,
  termTestSet   :: Map Schema (TestSet TermFrom),
  freshTestSet  :: TestSet TermFrom,
  proved        :: Set (PropOf PruningTerm),
  discovered    :: [Prop],
  kind          :: Type -> TypeKind }

data Event =
    Schema Origin (Poly Schema) (KindOf Schema)
  | Term   TermFrom      (KindOf TermFrom)
  | ConsiderSchema Origin (Poly Schema)
  | ConsiderTerm   TermFrom
  | Type           (Poly Type)
  | UntestableType (Poly Type)
  | Found          Prop
  | InstantiateSchema Schema Schema
  | FinishedSize   Int
  deriving (Eq, Ord)

data Origin = Original | PolyInstance deriving (Eq, Ord)

instance Pretty Event where
  pretty (Schema o s k) = text "schema" <+> pretty s <> text "," <+> pretty o <> text ":" <+> pretty k
  pretty (Term t k) = text "term" <+> pretty t <> text ":" <+> pretty k
  pretty (ConsiderSchema o s) = text "consider schema" <+> pretty s <+> text "::" <+> pretty (typ s) <> text "," <+> pretty o
  pretty (ConsiderTerm t) = text "consider term" <+> pretty t <+> text "::" <+> pretty (typ t)
  pretty (Type ty) = text "type" <+> pretty ty
  pretty (UntestableType ty) = text "untestable type" <+> pretty ty
  pretty (Found prop) = text "found" <+> pretty prop
  pretty (FinishedSize n) = text "finished size" <+> pretty n
  pretty (InstantiateSchema s s') = text "instantiate schema" <+> pretty s' <+> text "from" <+> pretty s

instance Pretty Origin where
  pretty Original = text "original"
  pretty PolyInstance = text "instance"

data KindOf a = Untestable | TimedOut | Representative | EqualTo a
  deriving (Eq, Ord)

instance Pretty a => Pretty (KindOf a) where
  pretty Untestable = text "untestable"
  pretty TimedOut = text "timed out"
  pretty Representative = text "representative"
  pretty (EqualTo x) = text "equal to" <+> pretty x

type Schemas = Map Int (Map (Poly Type) [Poly Schema])

initialState :: Signature -> [(QCGen, Int)] -> S
initialState sig seeds =
  S { schemas       = Map.empty,
      terms         = Set.empty,
      schemaTestSet = emptyTestSet (memo (makeTester specialise e seeds sig)),
      termTestSet   = Map.empty,
      freshTestSet  = emptyTestSet (memo (makeTester specialise e seeds sig)),
      proved        = Set.empty,
      discovered    = background sig,
      kind          = memo (typeKind sig) }
  where
    e = memo (env sig)

newTerm :: Term -> M ()
newTerm t = lift (modify (\s -> s { terms = Set.insert t (terms s) }))

schemasOfSize :: Int -> Signature -> M [Schema]
schemasOfSize n sig = do
  ss <- lift $ gets schemas
  return $
    [ Var (Hole (Var (TyVar 0))) | n == 1 ] ++
    [ Fun c [] | c <- constants sig, n == conSize c ] ++
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

quickSpecWithBackground :: Signature -> Signature -> IO Signature
quickSpecWithBackground sig1 sig2 = do
  thy <- quickSpec sig1
  quickSpec (thy `mappend` sig2)

incrementalQuickSpec :: Signature -> IO Signature
incrementalQuickSpec sig@Signature { constants = [] } = return sig
incrementalQuickSpec sig = do
  thy <- incrementalQuickSpec sig { constants = init (constants sig) }
  quickSpec sig { background = background thy,
                  constants = constants thy ++ [last (constants sig)] }

quickSpec :: Signature -> IO Signature
quickSpec sig0 = unbuffered $ do
  let sig = renumber sig0
  putStrLn "== Signature =="
  prettyPrint sig
  putStrLn ""
  runM sig $ do
    quickSpecLoop sig
    summarise
    props <- lift (gets (reverse . discovered))
    return sig {
      constants = [ c { conIsBackground = True } | c <- constants sig ],
      background = background sig ++ map (fmap (mapTerm (\c -> c { conIsBackground = True }) id)) props }

runM :: Signature -> M a -> IO a
runM sig m = do
  seeds <- fmap (take (maxTests_ sig)) (genSeeds 20)
  evalPruner sig (evalStateT (runRulesT m) (initialState sig seeds))

quickSpecLoop :: Signature -> M ()
quickSpecLoop sig = do
  createRules sig
  mapM_ (exploreSize sig) [1..maxTermSize_ sig]

exploreSize sig n = do
  lift $ modify (\s -> s { schemas = Map.insert n Map.empty (schemas s) })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  liftIO $ putStrLn ("Size " ++ show n ++ ", " ++ show (length ss) ++ " schemas to consider:")
  mapM_ (generate . ConsiderSchema Original . poly) ss
  generate (FinishedSize n)
  liftIO $ putStrLn ""

summarise :: M ()
summarise = do
  es <- getEvents
  let numEvents = length es
      numSchemas  = length [ () | Schema{} <- es ]
      numTerms    = length [ () | Term{}   <- es ]
      numCreation = length [ () | ConsiderSchema{} <- es ] + length [ () | ConsiderTerm{} <- es ]
      numMisc = numEvents - numSchemas - numTerms - numCreation
  h <- numHooks
  liftIO $ putStrLn (show numEvents ++ " events created in total (" ++
                     show numSchemas ++ " schemas, " ++
                     show numTerms ++ " terms, " ++
                     show numCreation ++ " creation, " ++
                     show numMisc ++ " miscellaneous).")
  liftIO $ putStrLn (show h ++ " hooks installed.\n")
  s <- lift (lift (liftPruner get))
  liftIO (putStr (pruningReport s))

allUnifications :: Term -> [Term]
allUnifications t = map f ss
  where
    vs = [ map (x,) (take 3 xs) | xs <- partitionBy typ (usort (vars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = rename (go s) t

createRules :: Signature -> M ()
createRules sig = do
  rule $ do
    Schema o s k <- event
    execute $ do
      unless (k == TimedOut || o == PolyInstance) $ accept s
      let ms = oneTypeVar (unPoly s)
      case k of
        TimedOut ->
          liftIO $ print (text "Schema" <+> pretty s <+> text "timed out")
        Untestable -> return ()
        EqualTo t -> do
          generate (InstantiateSchema t t)
          generate (InstantiateSchema t ms)
        Representative -> do
          generate (ConsiderTerm (From ms (instantiate ms)))
          when (size ms <= maxCommutativeSize_ sig) $
            generate (InstantiateSchema ms ms)

  rule $ do
    InstantiateSchema s s' <- event
    execute $
      considerRenamings s s'

  rule $ do
    Term (From s t) k <- event
    execute $ do
      let add = do
            u <- fmap (fromMaybe t) (lift (lift (rep t)))
            newTerm u
      case k of
        TimedOut -> do
          liftIO $ print (text "Term" <+> pretty t <+> text "timed out")
          add
        Untestable ->
          ERROR ("Untestable instance " ++ prettyShow t ++ " of testable schema " ++ prettyShow s)
        EqualTo (From _ u) -> do
          --t' <- fmap (fromMaybe t) (lift (lift (rep t)))
          let t' = t
          u' <- fmap (fromMaybe u) (lift (lift (rep u)))
          case orientTerms t' u' of
            Just _ -> do
              generate (Found ([] :=>: t' :=: u'))
              add
            Nothing -> do
              rule $ do
                FinishedSize n <- event
                require (n == size t)
                execute $ do
                  t' <- fmap (fromMaybe t) (lift (lift (rep t)))
                  u' <- fmap (fromMaybe u) (lift (lift (rep u)))
                  unless (t' == u') $ do
                    generate (Found ([] :=>: t' :=: u'))
                    add
        Representative -> add

  rule $ do
    ConsiderSchema o s <- event
    let ty = typ s
    kind <- execute $ lift $ gets kind
    require (kind ty /= Useless)
    require (and [ kind ty == Useful | t <- properSubterms (unPoly s) ])
    execute $
      case kind ty of
        Partial -> do
          generate (Schema o s Untestable)
          newTerm (instantiate (oneTypeVar (unPoly s)))
        Useful ->
          consider sig (Schema o s) (unPoly (oneTypeVar s))

  rule $ do
    ConsiderTerm t@(From _ t') <- event
    execute $ do
      consider sig (Term t) t

  rule $ do
    Schema _ s _ <- event
    execute $
      generate (Type (polyTyp s))

  rule $ do
    Type ty1 <- event
    Type ty2 <- event
    require (ty1 < ty2)
    Just mgu <- return (polyMgu ty1 ty2)
    let tys = [ty1, ty2] \\ [mgu]

    Schema Original s Representative <- event
    require (polyTyp s `elem` tys)

    execute $
      generate (ConsiderSchema PolyInstance (fromMaybe __ (cast (unPoly mgu) s)))

  rule $ do
    Schema _ s Untestable <- event
    require (arity (typ s) == 0)
    execute $
      generate (UntestableType (polyTyp s))

  rule $ do
    UntestableType ty <- event
    execute $
      liftIO $ putStrLn $
        "Warning: generated term of untestable type " ++ prettyShow ty

  rule $ do
    Found prop <- event
    execute $
      found sig prop

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

consider :: Considerable a => Signature -> (KindOf a -> Event) -> a -> M ()
consider sig makeEvent x = do
  let t = generalise x
  res   <- lift (lift (rep t))
  terms <- lift (gets terms)
  case res of
    Just u | u `Set.member` terms || canonicalise u `Set.member` terms -> return ()
    Nothing | t `Set.member` terms || canonicalise t `Set.member` terms -> return ()
    _ -> do
      case res of
        Nothing -> return ()
        Just u ->
          liftIO $ prettyPrint (text "Avoided reduction" <+> pretty (Rule t u))
      ts <- getTestSet x
      res <-
        liftIO . testTimeout_ sig $
        case insert x ts of
          Nothing -> return $ do
            generate (makeEvent Untestable)
          Just (Old y) -> return $ do
            generate (makeEvent (EqualTo y))
          Just (New ts) -> return $ do
            putTestSet x ts
            generate (makeEvent Representative)
      fromMaybe (generate (makeEvent TimedOut)) res

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
  otherTypesDL (From _ t) = otherTypesDL t
  typeSubst sub (From s t) = From s (typeSubst sub t)

instance Considerable TermFrom where
  generalise (From _ t) = t
  specialise (From _ t) = t
  getTestSet (From s _) = lift $ do
    ts <- gets freshTestSet
    gets (Map.findWithDefault ts s . termTestSet)
  putTestSet (From s _) ts =
    lift $ modify (\st -> st { termTestSet = Map.insert s ts (termTestSet st) })

found :: Signature -> Prop -> M ()
found sig prop0 = do
  let prop = regeneralise prop0
  props <- lift (gets discovered)
  (_, props') <- liftIO $ runPruner sig $ mapM_ axiom (map (simplify_ sig) props)

  res <- liftIO $ pruner (extraPruner_ sig) props' (toGoal (simplify_ sig prop))
  case res of
    True ->
      return ()
    False -> do
      lift $ modify (\s -> s { discovered = prop:discovered s })
      when (null (funs prop) || not (null (filter (not . conIsBackground) (funs prop)))) $
        liftIO $ putStrLn (prettyShow (prettyRename sig prop))

  lift (lift (axiom prop))
  terms <- fmap Set.toList (lift (gets terms))
  let rep' t = do
        u <- rep t
        return (fromMaybe t u)
  terms' <- mapM (lift . lift . rep') terms
  lift $ modify (\s -> s { terms = Set.fromList terms' })

pruner :: ExtraPruner -> [PropOf PruningTerm] -> PropOf PruningTerm -> IO Bool
pruner (SPASS timeout) = E.spassUnify timeout
pruner (E timeout) = E.eUnify timeout
pruner (Z3 timeout) = Z3.z3Unify timeout
pruner None = \_ _ -> return False

accept :: Poly Schema -> M ()
accept s = do
  lift $ modify (\st -> st { schemas = Map.adjust f (size (unPoly s)) (schemas st) })
  where
    f m = Map.insertWith (++) (polyTyp s) [s] m
