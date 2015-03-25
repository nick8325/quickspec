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
import QuickSpec.Pruning.Equation
import QuickSpec.Utils
import Test.QuickCheck.Random
import Test.QuickCheck.Text
import System.Random
import Data.Rewriting.Rule(Rule(Rule))
import Control.Spoon

type M = RulesT Event (StateT S (PrunerM PrunerType))

data S = S {
  schemas       :: Schemas,
  allSchemas    :: Set Term,
  terms         :: Set Term,
  schemaTestSet :: TestSet Schema,
  termTestSet   :: Map Schema (TestSet TermFrom),
  freshTestSet  :: TestSet TermFrom,
  proved        :: Set (PropOf PruningTerm),
  discovered    :: [Prop],
  delayed       :: [(Term, Term)],
  kind          :: Type -> TypeKind,
  terminal      :: Terminal }

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
  | Ignoring (RuleOf Term)
  deriving (Eq, Ord)

data Origin = Original | PolyInstance deriving (Eq, Ord)

instance Pretty Event where
  pretty (Schema o s k) = hang (text "schema" <+> pretty s <> text "," <+> pretty o <> text ":") 2 (pretty k)
  pretty (Term t k) = hang (text "term" <+> pretty t <> text ":") 2 (pretty k)
  pretty (ConsiderSchema o s) = text "consider schema" <+> pretty s <+> text "::" <+> pretty (typ s) <> text "," <+> pretty o
  pretty (ConsiderTerm t) = text "consider term" <+> pretty t <+> text "::" <+> pretty (typ t)
  pretty (Type ty) = text "type" <+> pretty ty
  pretty (UntestableType ty) = text "untestable type" <+> pretty ty
  pretty (Found prop) = text "found" <+> pretty prop
  pretty (FinishedSize n) = text "finished size" <+> pretty n
  pretty (InstantiateSchema s s') = sep [text "instantiate schema", nest 2 (pretty s'), text "from", nest 2 (pretty s)]
  pretty (Ignoring rule) = hang (text "ignoring") 2 (pretty rule)

instance Pretty Origin where
  pretty Original = text "original"
  pretty PolyInstance = text "instance"

data KindOf a = Untestable | TimedOut | Representative | EqualTo a EqualReason
  deriving (Eq, Ord)

data EqualReason = Testing | Pruning deriving (Eq, Ord)

instance Pretty a => Pretty (KindOf a) where
  pretty Untestable = text "untestable"
  pretty TimedOut = text "timed out"
  pretty Representative = text "representative"
  pretty (EqualTo x r) = sep [text "equal to", nest 2 (pretty x), text "by", nest 2 (pretty r)]

instance Pretty EqualReason where
  pretty Testing = text "testing"
  pretty Pruning = text "pruning"

type Schemas = Map Int (Map (Poly Type) [Poly Schema])

initialState :: Signature -> [(QCGen, Int)] -> Terminal -> S
initialState sig seeds terminal =
  S { schemas       = Map.empty,
      terms         = Set.empty,
      allSchemas    = Set.empty,
      schemaTestSet = emptyTestSet (memo (makeTester specialise v seeds2 sig)),
      termTestSet   = Map.empty,
      freshTestSet  = emptyTestSet (memo (makeTester specialise v seeds2 sig)),
      proved        = Set.empty,
      discovered    = background sig,
      delayed       = [],
      kind          = memo (typeKind sig),
      terminal      = terminal }
  where
    seeds1 = [ (fst (split g), n) | (g, n) <- seeds ]
    seeds2 = [ (snd (split g), n) | (g, n) <- seeds ]
    e = memo (env sig)
    v = [ memo (makeValuation e g n) | (g, n) <- seeds1 ]

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
quickSpec sig0 = do
  let sig = renumber sig0 { constants = idConstant:filter (/= idConstant) (constants sig0) }
  putStrLn "== Signature =="
  prettyPrint sig
  putStrLn ""
  putStrLn "== Laws =="
  runM sig $ do
    quickSpecLoop sig
    liftIO $ putStrLn "== Statistics =="
    summarise
    props <- lift (gets (reverse . discovered))
    theory <- lift (lift (liftPruner get))
    return sig {
      constants = [ c { conIsBackground = True } | c <- constants sig ],
      background = background sig ++ map (fmap (mapTerm (\c -> c { conIsBackground = True }) id)) props,
      theory = Just theory }

runM :: Signature -> M a -> IO a
runM sig m = withStdioTerminal $ \term -> do
  seeds <- fmap (take (maxTests_ sig)) (genSeeds 20)
  evalPruner sig
    (fromMaybe (emptyPruner sig) (theory sig))
    (evalStateT (runRulesT m) (initialState sig seeds term))

onTerm :: (Terminal -> String -> IO ()) -> String -> M ()
onTerm f s = do
  term <- lift (gets terminal)
  liftIO (f term s)

quickSpecLoop :: Signature -> M ()
quickSpecLoop sig = do
  createRules sig
  mapM_ (exploreSize sig) [1..maxTermSize_ sig]
  onTerm putLine ""

exploreSize sig n = do
  lift $ modify (\s -> s { schemas = Map.insert n Map.empty (schemas s), delayed = [] })
  ss <- fmap (sortBy (comparing measure)) (schemasOfSize n sig)
  let m = length ss
  forM_ (zip [1..] ss) $ \(i, s) -> do
    onTerm putTemp ("[testing schemas of size " ++ show n ++ ": " ++ show i ++ "/" ++ show m ++ "...]")
    generate (ConsiderSchema Original (poly s))

  let measureEquation (t, u) = (measure t, measure u)
  del <- lift $ gets delayed
  lift $ modify (\s -> s { delayed = [] })
  forM_ (sortBy (comparing measureEquation) del) $ \(t, u) -> do
    t' <- fmap (fromMaybe t) (lift (lift (rep t)))
    u' <- fmap (fromMaybe u) (lift (lift (rep u)))
    unless (t' == u') $ do
      generate (Found ([] :=>: t' :=: u'))
    newTerm u'

summarise :: M ()
summarise = do
  es <- getEvents
  sts <- lift $ gets schemaTestSet
  tts <- lift $ gets termTestSet
  let numEvents = length es
      numSchemas  = length [ () | Schema _ _ k <- es, tested k ]
      tested Untestable = False
      tested (EqualTo _ Pruning) = False
      tested _ = True
      numTerms    = length [ () | Term _ k <- es ]
      numCreation = length [ () | ConsiderSchema{} <- es ] + length [ () | ConsiderTerm{} <- es ]
      numMisc = numEvents - numSchemas - numTerms - numCreation
      schemaTests = numTests sts
      schemaReps = QuickSpec.TestSet.numTerms sts
      termTests = sum (map numTests (Map.elems tts))
      termReps = sum (map QuickSpec.TestSet.numTerms (Map.elems tts))
      equalSchemas = length [ () | Schema _ _ (EqualTo _ Testing) <- es ]
      equalTerms = length [ () | Term _ (EqualTo _ Testing) <- es ]
  h <- numHooks
  liftIO $ putStrLn (show numEvents ++ " events created in total (" ++
                     show numSchemas ++ " schemas, " ++
                     show numTerms ++ " terms, " ++
                     show numCreation ++ " creation, " ++
                     show numMisc ++ " miscellaneous), " ++
                     show h ++ " hooks.")
  liftIO $ putStrLn (show schemaTests ++ " schema test cases for " ++ show schemaReps ++ " representative schemas.")
  liftIO $ putStrLn (show termTests ++ " term test cases for " ++ show termReps ++ " representative terms.")
  liftIO $ putStrLn (show equalSchemas ++ " equal schemas and " ++ show equalTerms ++ " equal terms generated.")
  s <- lift (lift (liftPruner get))
  liftIO (putStrLn (pruningReport s))
  liftIO (putStrLn "")

allUnifications :: Term -> [Term]
allUnifications t = map f ss
  where
    vs = [ map (x,) (take 4 xs) | xs <- partitionBy typ (usort (vars t)), x <- xs ]
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
        EqualTo t _ -> do
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
        EqualTo (From _ u) _ -> do
          --t' <- fmap (fromMaybe t) (lift (lift (rep t)))
          let t' = t
          u' <- fmap (fromMaybe u) (lift (lift (rep u)))
          del <- lift $ gets delayed
          let wait = or [ isJust (match2 (x, y) (t, u)) | (x, y) <- del ]
              match2 (x, y) (t, u) = match (Fun f [x, y]) (Fun f [t, u])
              f = head (funs t ++ funs u)
          case orientTerms t' u'  of
            Just _ | not wait -> do
              generate (Found ([] :=>: t' :=: u'))
              add
            _ -> do
              lift $ modify (\s -> s { delayed = (t, u):delayed s })
        Representative -> add

  rule $ do
    ConsiderSchema o s <- event
    let ty = typ s
    kind <- execute $ lift $ gets kind
    require (kind ty /= Useless)
    require (and [ kind (typ t) == Useful | t <- properSubterms (unPoly s) ])
    execute $
      case kind ty of
        Partial -> do
          generate (Schema o s Untestable)
          newTerm (instantiate (oneTypeVar (unPoly s)))
        Useful ->
          consider sig (Schema o s) (unPoly (oneTypeVar s))

  rule $ do
    ConsiderTerm t@(From _ t') <- event
    -- Check if term is LHS of a delayed law
    del <- execute $ lift $ gets delayed
    terms <- execute $ lift $ gets terms
    let delayed = not . null $ do
          (x, y) <- del
          sub <- maybeToList (match x t')
          let u = subst sub y
          guard (u `Set.member` terms)
    unless delayed $
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
    kind <- execute $ lift $ gets kind
    Just mgu <- return (polyMgu ty1 ty2)
    require (kind (unPoly mgu) == Useful)
    let tys = [ty | ty <- [ty1, ty2], oneTypeVar ty /= oneTypeVar mgu]

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

  let printing _ = False

  rule $ do
    x <- event
    require (printing x)
    execute $ liftIO $ prettyPrint x

considerRenamings :: Schema -> Schema -> M ()
considerRenamings s s' = do
  sequence_ [ generate (ConsiderTerm (From s t)) | t <- ts ]
  where
    ts = sortBy (comparing measure) (allUnifications (instantiate s'))

class (Eq a, Typed a) => Considerable a where
  generalise   :: a -> Term
  specialise   :: a -> Term
  unspecialise :: a -> Term -> a
  getTestSet   :: a -> M (TestSet a)
  putTestSet   :: a -> TestSet a -> M ()
  findAll      :: a -> M (Set Term)

consider :: Considerable a => Signature -> (KindOf a -> Event) -> a -> M ()
consider sig makeEvent x = do
  let t = generalise x
  res   <- lift (lift (rep t))
  terms <- lift (gets terms)
  allSchemas <- findAll x
  case res of
    Just u | u `Set.member` terms -> return ()
    Nothing | t `Set.member` terms -> return ()
    _ -> do
      case res of
        Just u -> generate (Ignoring (Rule t u))
        _ -> return ()
      let t' = specialise x
      res' <- lift (lift (rep t'))
      case res' of
        Just u' | u' `Set.member` allSchemas ->
          generate (makeEvent (EqualTo (unspecialise x u') Pruning))
        Nothing | t' `Set.member` allSchemas ->
          generate (makeEvent (EqualTo (unspecialise x t') Pruning))
        _ -> do
          ts <- getTestSet x
          res <-
            liftIO . testTimeout_ sig $
            case fmap teaspoon (insert x ts) of
              Nothing -> return $ do
                generate (makeEvent Untestable)
              Just Nothing -> return $ return () -- partial term
              Just (Just (Old y)) -> return $ do
                generate (makeEvent (EqualTo y Testing))
              Just (Just (New ts)) -> return $ do
                putTestSet x ts
                generate (makeEvent Representative)
          fromMaybe (generate (makeEvent TimedOut)) res

instance Considerable Schema where
  generalise      = instantiate . oneTypeVar
  specialise      = skeleton . generalise
  unspecialise _  = rename (Hole . typ)
  getTestSet _    = lift $ gets schemaTestSet
  putTestSet _ ts = lift $ modify (\s -> s { schemaTestSet = ts })
  findAll _       = lift (gets allSchemas)

data TermFrom = From Schema Term deriving (Eq, Ord, Show)

instance Pretty TermFrom where
  pretty (From s t) = pretty t <+> text "from" <+> pretty s

instance Typed TermFrom where
  typ (From _ t) = typ t
  otherTypesDL (From _ t) = otherTypesDL t
  typeSubst sub (From s t) = From s (typeSubst sub t)

instance Considerable TermFrom where
  generalise   (From _ t) = t
  specialise   (From _ t) = t
  unspecialise (From s _) t = From s t
  getTestSet (From s _) = lift $ do
    ts <- gets freshTestSet
    gets (Map.findWithDefault ts s . termTestSet)
  putTestSet (From s _) ts =
    lift $ modify (\st -> st { termTestSet = Map.insert s ts (termTestSet st) })
  findAll _ = return Set.empty

found :: Signature -> Prop -> M ()
found sig prop0 = do
  let reorder (lhs :=>: t :=: u)
        | measure t >= measure u = lhs :=>: t :=: u
        | otherwise = lhs :=>: u :=: t
      prop = regeneralise (reorder prop0)
  props <- lift (gets discovered)
  (_, props') <- liftIO $ runPruner sig [] $ mapM_ (axiom Normal) (map (simplify_ sig) props)

  let props = etaExpand prop
  onTerm putTemp "[running extra pruner...]"
  res <- liftIO $ pruner (extraPruner_ sig) props' (toGoal (simplify_ sig prop))
  case res of
    True ->
      return ()
    False -> do
      lift $ modify (\s -> s { discovered = props ++ discovered s })
      let (prop':_) = filter isPretty props ++ [prop]
          isPretty (_ :=>: t :=: u) = isPretty1 t && isPretty1 u
          isPretty1 (Fun f ts) | undersaturated (conStyle f) (length ts) = False
          isPretty1 _ = True
          undersaturated Invisible 0 = True
          undersaturated (Tuple m) n | m > n = True
          undersaturated (Infix _) n | n < 2 = True
          undersaturated (Infixr _) n | n < 2 = True
          undersaturated Prefix 0 = True
          undersaturated Postfix 0 = True
          undersaturated Gyrator n | n < 2 = True
          undersaturated _ _ = False
          rename prop@(lhs :=>: t :=: u)
            | t `isVariantOf` u = lhs' :=>: u' :=: t'
            | otherwise = prettyRename sig prop
            where
              lhs' :=>: t' :=: u' = prettyRename sig prop
      when (null (funs prop') || not (null (filter (not . conIsBackground) (funs prop')))) $
        onTerm putLine (prettyShow (rename (canonicalise prop')))

  onTerm putTemp "[completing theory...]"
  mapM_ (lift . lift . axiom Normal) props
  forM_ (map canonicalise props) $ \(_ :=>: _ :=: t) -> do
    u <- fmap (fromMaybe t) (lift (lift (rep t)))
    newTerm u
  onTerm putTemp "[renormalising existing terms...]"
  let norm s = do
        ts <- filterM (fmap isJust . rep) (Set.toList s)
        us <- mapM (fmap (fromMaybe __) . rep) ts
        return ((s Set.\\ Set.fromList ts) `Set.union` Set.fromList us)
  terms <- lift (gets terms) >>= lift . lift . norm
  allSchemas <- lift (gets allSchemas) >>= lift . lift . norm
  lift $ modify (\s -> s { terms = terms, allSchemas = allSchemas })
  onTerm putPart ""

etaExpand :: Prop -> [Prop]
etaExpand prop@(lhs :=>: t :=: u) =
  prop:
  case (typ t, tryApply t x, tryApply u x) of
    (Fun Arrow _, Just t', Just u') -> etaExpand (lhs :=>: t' :=: u')
    _ -> []
  where
    x = Var (Variable n (head (typeArgs (typ t) ++ [typeOf ()])))
    n = succ (maximum (0:map varNumber (vars prop)))

pruner :: ExtraPruner -> [PropOf PruningTerm] -> PropOf PruningTerm -> IO Bool
pruner (SPASS timeout) = E.spassUnify timeout
pruner (E timeout) = E.eUnify timeout
pruner (Z3 timeout) = Z3.z3Unify timeout
pruner None = \_ _ -> return False

accept :: Poly Schema -> M ()
accept s = do
  let t = skeleton (instantiate (unPoly s))
  u <- fmap (fromMaybe t) (lift . lift . rep $ t)
  lift $ modify (\st -> st { schemas = Map.adjust f (size (unPoly s)) (schemas st),
                             allSchemas = Set.insert u (allSchemas st) })
  where
    f m = Map.insertWith (++) (polyTyp s) [s] m
