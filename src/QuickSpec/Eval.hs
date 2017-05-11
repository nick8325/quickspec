-- | The main 'quickSpec' function lives here.
{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, TupleSections, FlexibleContexts, DoAndIfThenElse #-}
module QuickSpec.Eval where

#include "errors.h"
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
import qualified QuickSpec.Pruning.Waldmeister as WM
import QuickSpec.Rules
import QuickSpec.Signature
import QuickSpec.Term
import QuickSpec.Test
import QuickSpec.TestSet
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.PrintConditionally
import QuickSpec.PredicatesInterface hiding (size)
import Test.QuickCheck.Random
import Test.QuickCheck.Text
import System.Random
import Control.Spoon
import Twee.Base hiding (terms)
import Twee.Rule(Rule(Rule))
import qualified Twee.Rule as Rule
import Text.Printf

type M = RulesT Event (StateT S (PrunerM PrunerType))

data S = S {
  schemas       :: Schemas,
  allSchemas    :: Set (Term Constant),
  terms         :: Set (Term Constant),
  schemaTestSet :: TestSet (Term Constant),
  termTestSet   :: Map (Term Constant) (TestSet TermFrom),
  trueTerm      :: !(Term Constant),
  freshTestSet  :: TestSet TermFrom,
  proved        :: (Set PruningProp),
  discovered    :: ([Prop]),
  howMany       :: Int,
  delayed       :: [(Term Constant, Term Constant)],
  kind          :: Type -> TypeKind,
  terminal      :: Terminal }

-- | Internal QuickSpec event.
data Event =
    Schema Origin (Poly (Term Constant)) (KindOf (Term Constant))
  | Term   TermFrom      (KindOf TermFrom)
  | ConsiderSchema Origin (Poly (Term Constant))
  | ConsiderTerm   TermFrom
  | Type           (Poly Type)
  | UntestableType (Poly Type)
  | Found          Prop
  | InstantiateSchema (Term Constant) (Term Constant)
  | FinishedSize   Int
  | Ignoring (Rule Constant)
  deriving (Eq, Ord)

data Origin = Original | PolyInstance deriving (Eq, Ord)

instance Pretty Event where
  pPrint (Schema o s k) = hang (text "schema" <+> pPrint s <> text "," <+> pPrint o <> text ":") 2 (pPrint k)
  pPrint (Term t k) = hang (text "term" <+> pPrint t <> text ":") 2 (pPrint k)
  pPrint (ConsiderSchema o s) = text "consider schema" <+> pPrint s <+> text "::" <+> pPrint (typ s) <> text "," <+> pPrint o
  pPrint (ConsiderTerm t) = text "consider term" <+> pPrint t <+> text "::" <+> pPrint (typ t)
  pPrint (Type ty) = text "type" <+> pPrint ty
  pPrint (UntestableType ty) = text "untestable type" <+> pPrint ty
  pPrint (Found prop) = text "found" <+> pPrint prop
  pPrint (FinishedSize n) = text "finished size" <+> pPrint n
  pPrint (InstantiateSchema s s') = sep [text "instantiate schema", nest 2 (pPrint s'), text "from", nest 2 (pPrint s)]
  pPrint (Ignoring rule) = hang (text "ignoring") 2 (pPrint rule)

instance Pretty Origin where
  pPrint Original = text "original"
  pPrint PolyInstance = text "instance"

data KindOf a = Untestable | TimedOut | Representative | EqualTo a EqualReason
  deriving (Eq, Ord)

data EqualReason = Testing | Pruning deriving (Eq, Ord)

instance Pretty a => Pretty (KindOf a) where
  pPrint Untestable = text "untestable"
  pPrint TimedOut = text "timed out"
  pPrint Representative = text "representative"
  pPrint (EqualTo x r) = sep [text "equal to", nest 2 (pPrint x), text "by", nest 2 (pPrint r)]

instance Pretty EqualReason where
  pPrint Testing = text "testing"
  pPrint Pruning = text "pruning"

type Schemas = Map Int (Map (Poly Type) [Poly (Term Constant)])

initialState :: Signature -> [(QCGen, Int)] -> Terminal -> S
initialState sig seeds terminal =
  S { schemas       = Map.empty,
      terms         = Set.empty,
      allSchemas    = Set.empty,
      schemaTestSet = emptyTestSet (memo (makeTester specialise v seeds2 sig)),
      termTestSet   = Map.empty,
      trueTerm      = build (con (toFun (constant "True" True))),
      freshTestSet  = emptyTestSet (memo (makeTester specialise v seeds2 sig)),
      proved        = Set.empty,
      discovered    = background sig,
      howMany       = 0,
      delayed       = [],
      kind          = memo (typeKind sig),
      terminal      = terminal }
  where
    seeds1 = [ (fst (split g), n) | (g, n) <- seeds ]
    seeds2 = [ (snd (split g), n) | (g, n) <- seeds ]
    e = memo (env sig)
    v = [ memo2 (makeValuation e g n) | (g, n) <- seeds1 ]
    memo2 :: (Ord a, Ord b) => (a -> b -> c) -> a -> b -> c
    memo2 f = curry (memo (uncurry f))

newTerm :: Term Constant -> M ()
newTerm t = lift (modify (\s -> s { terms = Set.insert t (terms s) }))

schemasOfSize :: Int -> Signature -> M [Term Constant]
schemasOfSize n sig = do
  ss <- lift $ gets schemas
  let varty = build (var (MkVar 0))
      vartm = build (fun (toFun (Id varty)) [var (MkVar 0)])
  return $
    [ vartm | n == 1 ] ++
    [ app c [] | c <- constants sig, n == conSize c ] ++
    [ unPoly (apply f x)
    | i <- [0..n-1],
      let j = n-i,
      (fty, fs) <- Map.toList =<< maybeToList (Map.lookup i ss),
      canApply fty (poly varty),
      or [ canApply f (poly vartm) | f <- fs ],
      (xty, xs) <- (Map.toList =<< maybeToList (Map.lookup j ss)) ++ [ (poly varty, [poly vartm]) | n == 1 ],
      canApply fty xty,
      f <- fs,
      canApply f (poly vartm),
      x <- xs,
      case maxTermDepth sig of { Nothing -> True; Just d -> depth (unPoly x) <= d } ]

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

chopUpSignature :: [(Constant, [Int])] -> Signature -> [Signature -> Signature]
chopUpSignature cs sig0 = id:map phase phases
  where
    phase n sig =
      sig {
        constants = constants sig0 ++ [ c | (c, ns) <- cs, n `elem` ns ] }
    phases = usort (concatMap snd cs)

choppyQuickSpec :: [(Constant, [Int])] -> Signature -> IO Signature
choppyQuickSpec cs sig = do
  foldr (>=>) return (map (quickSpec .) sigs) sig
  where
   sigs = chopUpSignature cs sig

-- | Run QuickSpec. The returned signature contains the discovered
-- equations. By using |mappend| to combine the returned signature
-- and a new signature, you can use the discovered equations as
-- background theory in a later run of QuickSpec.
quickSpec :: Signature -> IO Signature
quickSpec sigin = do
  let sig = predicateSig sigin
  unless (silent sig) $ do
    putStrLn "== Signature =="
    prettyPrint sig
    putStrLn ""
    putStrLn "== Laws =="
  runM sig $ do
    quickSpecLoop sig
    when (not (silent sig) && printStatistics sig) $ do
      liftIO $ putStrLn "== Statistics =="
      summarise
    props <- lift (gets (reverse . discovered))
    theory <- lift (lift (liftPruner get))
    return sig {
      constants = [ c { conIsBackground = True } | c <- constants sig ],
      -- XXX
      background = background sig ++ props,
      theory = Just theory }

runM :: Signature -> M a -> IO a
runM sig m = withTerminal $ \term -> do
  seeds <- fmap (take (maxTests_ sig)) (genSeeds 20)
  evalPruner sig
    (fromMaybe (emptyPruner sig) (theory sig))
    (evalStateT (runRulesT m) (initialState sig seeds term))
  where
    withTerminal =
      if silent sig
      then withNullTerminal
      else withStdioTerminal

onTerm :: (Terminal -> String -> IO ()) -> String -> M ()
onTerm f s = do
  term <- lift (gets terminal)
  liftIO (f term s)

-- | Explore each size up to the maximum term size.
quickSpecLoop :: Signature -> M ()
quickSpecLoop sig = do
  createRules sig
  mapM_ (exploreSize sig) [minTermSize sig..maxTermSize_ sig]
  onTerm putLine ""

minTermSize :: Signature -> Int
minTermSize sig =
  minimum (1:map conSize (constants sig))

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
    t' <- normalise t
    u' <- normalise u
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

allUnifications :: Term Constant -> [Term Constant]
allUnifications t = map f ss
  where
    vs = [ map (x,) (take (varCount x) xs) | xs <- partitionBy fst (usort (typedVars t)), x <- xs ]
    ss = map Map.fromList (sequence vs)
    go s x = Map.findWithDefault __ x s
    f s = typedSubst (curry (typedVar . go s)) t
    typedVar (ty, x) = fun (toFun (Id ty)) [var x]
    varCount (ty, _) = 4

-- | Create the rules for processing QuickSpec events.
createRules :: Signature -> M ()
createRules sig = do
  -- NOTES:
  --  * Rules use event to signal which event they want to match.
  --  * Rules can overlap, so multiple rules can match different events.
  --    They will be executed in order of declaration.
  --  * An event can be generated repeatedly but will be ignored after the first time.

  -- A new schema was discovered.
  rule $ do
    Schema o s k <- event
    execute $ do
      unless (k == TimedOut || o == PolyInstance) $ accept s
      let ms = oneTypeVar (unPoly s)
      case k of
        TimedOut ->
          liftIO $ print (text "Schema" <+> pPrint s <+> text "timed out")
        Untestable -> return ()
        EqualTo t _ -> do
          generate (InstantiateSchema t t)
          generate (InstantiateSchema t ms)
        Representative -> do
          generate (ConsiderTerm (From ms (instantiate ms)))
          when (size ms <= maxCommutativeSize_ sig) $
            generate (InstantiateSchema ms ms)

  -- Instantiate a Schema
  -- Creates events for considering terms of that schema:
  --   for schema _ + _
  --   terms:     x + x, x + y, y + x, ...
  rule $ do
    InstantiateSchema s s' <- event
    execute $
      considerRenamings s s'

  rule $ do
    Term (From s t) k <- event
    execute $ do
      let add = do
            u <- normalise t
            newTerm u
      case k of
        TimedOut -> do
          liftIO $ print (text "Term" <+> pPrint t <+> text "timed out")
          add
        Untestable ->
          ERROR("Untestable instance " ++ prettyShow t ++ " of testable schema " ++ prettyShow s)
        EqualTo (From _ u) _ -> do
          --t' <- fmap (fromMaybe t) (lift (lift (rep t)))
          let t' = t
          -- u' <- normalise u
              u' = u
          del <- lift $ gets delayed
          let wait = or [ isJust (matchList (buildList [x, y]) (buildList [t, u])) | (x, y) <- del ]
              f = head (funs t ++ funs u)
              munge = build . extended . singleton . typedSubst (\_ x -> var x)
          case orientTerms (munge t') (munge u') of
            Just dir | not wait -> do
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
    require (and [ kind (typ t) == Useful | t@Fun{} <- properSubterms (unPoly s) ])
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
    require (typeArity (typ s) == 0)
    execute $
      generate (UntestableType (polyTyp s))

  rule $ do
    UntestableType ty <- event
    unless (silent sig) $
      execute $
      liftIO $ putStrLn $
        "Warning: generated term of untestable type " ++ prettyShow ty

  -- An equation was found, we should (possibly) print it.
  rule $ do
    Found prop <- event
    execute $
      found sig prop

  let printing _ = False

  -- Debug: print the received event, if the
  -- function 'printing' (defined above) returns True
  rule $ do
    x <- event
    require (printing x)
    execute $ liftIO $ prettyPrint x

considerRenamings :: Term Constant -> Term Constant -> M ()
considerRenamings s s' = do
  sequence_ [ generate (ConsiderTerm (From s t)) | t <- ts ]
  where
    ts = sortBy (comparing measure) (allUnifications (instantiate s'))

class (Eq a, Typed a, Pretty a) => Considerable a where
  -- | Returns the most general version, e.g.:
  --
  --   * Given the schema @_ + _@, returns @x + y@
  --   * Given the term   @x + x@, returns @x + x@
  generalise   :: a -> Term Constant


  -- | Returns the most specific version, e.g.:
  --
  --   * Given the schema @_ + _@, returns @x + x@
  --   * Given the term   @x + y@, returns @x + y@
  specialise   :: a -> Term Constant

  unspecialise :: a -> Term Constant -> a
  getTestSet   :: a -> M (TestSet a)
  putTestSet   :: a -> TestSet a -> M ()
  findAll      :: a -> M (Set (Term Constant))

-- | Tries to normalise a term using the current rewrite rules.
-- If the term is already in normal form, returns Nothing.
maybeNormalise :: Term Constant -> M (Maybe (Term Constant))
maybeNormalise = lift . lift . rep

-- | Normalises a term using the current rewrite rules.
normalise :: Term Constant -> M (Term Constant)
normalise t = fmap (fromMaybe t) (maybeNormalise t)

-- | Considers a Schema (@_ + _@) or a Term (@x + y@) and either
-- discards it or creates the relevant events.
consider :: Considerable a => Signature -> (KindOf a -> Event) -> a -> M ()
consider sig makeEvent x = do
  let t = generalise x
  res   <- maybeNormalise t
  terms <- lift (gets terms)
  allSchemas <- findAll x
  case res of
    Just u  | u `Set.member` terms -> do
      conditionalised <- considerConditionalising False sig ([] :=>: t :=: u)
      if not conditionalised then
        do
          let specx = specialise x
          res' <- maybeNormalise specx
          case res' of
            Nothing -> return ()
            Just u  -> void $ considerConditionalising False sig ([] :=>: specx :=: u)
      else
        return ()
    Nothing | t `Set.member` terms -> return ()
    _ -> do
      case res of
        Just u -> generate (Ignoring (Rule Rule.Oriented t u))
        _ -> return ()
      u' <- normalise (specialise x)
      if u' `Set.member` allSchemas
        then generate (makeEvent (EqualTo (unspecialise x u') Pruning))
        else do
          ts <- getTestSet x
          res <-
            liftIO . testTimeout_ sig $
            case fmap teaspoon (insert x ts) of
              Nothing -> return $ do
                generate (makeEvent Untestable)
              Just Nothing -> return (return ()) -- partial term
              Just (Just (Old y)) -> return $ do
                generate (makeEvent (EqualTo y Testing))
              Just (Just (New ts)) -> return $ do
                putTestSet x ts
                generate (makeEvent Representative)
          fromMaybe (generate (makeEvent TimedOut)) res

instance Considerable (Term Constant) where
  generalise      = instantiate . oneTypeVar
  specialise      = skeleton . generalise
  unspecialise _  = subst (const (var (MkVar 0)))
  getTestSet _    = lift $ gets schemaTestSet
  putTestSet _ ts = lift $ modify (\s -> s { schemaTestSet = ts })
  findAll _       = lift (gets allSchemas)

data TermFrom = From (Term Constant) (Term Constant) deriving (Eq, Ord, Show)

instance Pretty TermFrom where
  pPrint (From s t) = pPrint t <+> text "from" <+> pPrint s

instance Typed TermFrom where
  typ (From _ t) = typ t
  otherTypesDL (From _ t) = otherTypesDL t
  typeReplace sub (From s t) = From s (typeReplace sub t)

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

shouldPrint :: Prop -> Bool
shouldPrint prop =
  null (funs prop) || not (null (filter (not . conIsBackground_ . fromFun) (funs prop)))
  where
    conIsBackground_ (Id _) = True
    conIsBackground_ (Apply _) = True
    conIsBackground_ con = conIsBackground con

considerConditionalising :: Bool -> Signature -> Prop -> M Bool
considerConditionalising regeneralised sig prop0 = do
  let prop = if regeneralised then prop0 else regeneralise prop0

  -- If we have discovered that "somePredicate x_1 x_2 ... x_n = True"
  -- we should add the axiom "get_x_n (toSomePredicate x_1 x_2 ... x_n) = x_n"
  -- to the set of known equations
  truth <- lift $ gets trueTerm 
  case prop of
    (lhs :=>: t :=: u) ->
      if u == truth then
          case t of
            App f ts -> case lookupPredicate f (predicates sig) of -- It is an interesting predicate, i.e. it was added by the user
              Just prd -> do
                    -- Get the `p_n` selector
                let selector i = fromJust $ cast (selType i) $ sel i
                    sel i      = app (selectors prd !! i) []
                    emb        = fromJust $ cast embedderType $ app (embedder prd) []

                    testCase   = head $ typeArgs $ typ $ sel 0

                    -- Make sure the selector and embedder functions are casted to have the
                    -- types corresponding to the types in `ts`
                    castTestCase (App x [s, _]) = app x [s, arrowType (map typ ts) (typeOf True)]
                    selType i = app Arrow [castTestCase testCase, typ (ts !! i)]
                    embedderType = arrowType (map typ ts) (castTestCase testCase)

                    -- The "to_p x1 x2 ... xm" term
                    construction = foldl apply emb ts
                    -- The "p_n (to_p x1 x2 ... xn ... xm) = xn"
                    -- equations
                    equations = [ lhs :=>: apply (selector i) construction :=: x | (x, i) <- zip ts [0..]]

                let normFilter (_ :=>: a :=: b) = (/=) <$> normalise a <*> normalise b
                
                equations' <- filterM normFilter equations

                -- Declare the relevant equations as axioms
                -- This is "safe" because the equations do not result from testing
                -- (the unsafe is a bit strange, it _probably_ won't crash...)
                lift $ lift $ mapM (unsafeAxiom Normal) equations' 
                 
                return True 
              _ -> return True 
            _ -> do
              lift $ modify $ \st -> st {trueTerm = t} -- This is the smallest term equal to `True`
              return True 
        else
          return False
    _ -> return False

found :: Signature -> Prop -> M ()
found sig prop0 =  do
  let reorder (lhs :=>: t :=: u)
        | measure t >= measure u = lhs :=>: t :=: u
        | otherwise = lhs :=>: u :=: t
      prop = regeneralise (reorder prop0)

  props <- lift (gets discovered)
  (_, props') <- liftIO $ runPruner sig [] $ mapM_ (axiom Normal) (map (simplify_ sig) props)

  let prop' = etaExpand prop
  onTerm putTemp "[running extra pruner...]"
  res <- liftIO $ pruner (extraPruner_ sig) props' (toGoal (simplify_ sig prop))
  case res of
    True ->
      return ()
    False -> do
      lift $ modify (\s -> s { discovered = prop':discovered s })
      let isPretty (_ :=>: t :=: u) = isPretty1 t && isPretty1 u
          isPretty1 (App f ts) | undersaturated (conStyle f) (length ts) = False
          isPretty1 _ = True
          -- XXX
          -- undersaturated Invisible 0 = True
          -- undersaturated (Tuple m) n | m > n = True
          -- undersaturated (Infix _) n | n < 2 = True
          -- undersaturated (Infixr _) n | n < 2 = True
          -- undersaturated Prefix 0 = True
          -- undersaturated Postfix 0 = True
          -- undersaturated Gyrator n | n < 2 = True
          undersaturated _ _ = False
          rename prop@(lhs :=>: t :=: u)
            | t `isVariantOf` u = lhs' :=>: u' :=: t'
            | otherwise = prettyRename sig prop
            where
              lhs' :=>: t' :=: u' = prettyRename sig prop
      when (shouldPrint prop') $ do
        lift $ modify (\s -> s { howMany = howMany s + 1 })
        n <- lift $ gets howMany
        onTerm putLine $ show $
          text (printf "%3d." n) <+>
          pPrint (rename (canonicalise (conditionalise (conditionalsContext sig)  prop')))

  onTerm putTemp "[completing theory...]"
  lift (lift (axiom Normal prop))
  let _ :=>: _ :=: t = canonicalise prop
  u <- normalise t
  newTerm u
  onTerm putTemp "[renormalising existing terms...]"
  let norm s = do
                 ts <- filterM (fmap isJust . rep) (Set.toList s)
                 us <- mapM (fmap (fromMaybe __) . rep) ts
                 return ((s Set.\\ Set.fromList ts) `Set.union` Set.fromList us)
  terms <- lift (gets terms) >>= lift . lift . norm
  allSchemas <- lift (gets allSchemas) >>= lift . lift . norm
  lift $ modify (\s -> s { terms = terms, allSchemas = allSchemas })
  considerConditionalising True sig prop
  onTerm putPart ""

etaExpand :: Prop -> Prop
etaExpand prop@(lhs :=>: t :=: u) =
  case (tryApply t x, tryApply u x) of
    (Just t', Just u') -> etaExpand (lhs :=>: t' :=: u')
    _ -> prop
  where
    x = build (fun (toFun (Id (head (typeArgs (typ t) ++ [typeOf ()])))) [var (MkVar n)])
    n = boundList (buildList (map var (vars prop)))

pruner :: ExtraPruner -> [PruningProp] -> PruningProp -> IO Bool
pruner (SPASS timeout) = E.spassUnify timeout
pruner (E timeout) = E.eUnify timeout
pruner (Z3 timeout) = Z3.z3Unify timeout
pruner (Waldmeister timeout) = WM.wmUnify timeout
pruner None = \_ _ -> return False

accept :: Poly (Term Constant) -> M ()
accept s = do
  let t = skeleton (instantiate (unPoly s))
  u <- normalise t
  lift $ modify (\st -> st { schemas = Map.adjust f (size (unPoly s)) (schemas st),
                             allSchemas = Set.insert u (allSchemas st) })
  where
    f m = Map.insertWith (++) (polyTyp s) [s] m
