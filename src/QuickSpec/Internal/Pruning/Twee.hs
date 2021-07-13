-- A pruner that uses twee.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, GADTs, PatternSynonyms, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances, BangPatterns #-}
module QuickSpec.Internal.Pruning.Twee where

import QuickSpec.Internal.Testing
import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import Data.Lens.Light
import qualified Twee
import qualified Twee.Equation as Twee
import qualified Twee.KBO as KBO
import qualified Twee.Base as Twee
import Twee hiding (Config(..))
import Twee.Rule hiding (normalForms)
import Twee.Proof hiding (Config, defaultConfig, axiom)
import Twee.Base(Ordered(..), Labelled)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict hiding (State)
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import QuickSpec.Internal.Terminal
import qualified Data.Set as Set
import Data.Set(Set)
import Data.List

data Config =
  Config {
    cfg_max_term_size :: Int,
    cfg_max_cp_depth :: Int }

lens_max_term_size = lens cfg_max_term_size (\x y -> y { cfg_max_term_size = x })
lens_max_cp_depth = lens cfg_max_cp_depth (\x y -> y { cfg_max_cp_depth = x })

data Extended fun =
  Minimal |
  Skolem Int |
  Function fun Int |
  Tag Type |
  Apply Type
  deriving (Eq, Ord, Typeable)

instance (Ord fun, Typeable fun) => Labelled (Extended fun)

instance Sized fun => Sized (Extended fun) where
  size (Function f _) = size f
  size (Apply _) = 0
  size (Tag _) = 0
  size _ = 1

instance KBO.Sized (Extended fun) where
  size (Function _ _) = 1
  size (Apply _) = 0
  size (Tag _) = 1
  size _ = 1

instance (Ord fun, Typeable fun) => Twee.Minimal (Extended fun) where
  minimal = Twee.fun Minimal

instance EqualsBonus (Extended fun)

instance (Ord fun, Typeable fun, Pretty fun) => Pretty (Extended fun) where
  pPrintPrec l p (Function f n) = pPrintPrec l p f <#> pPrint n
  pPrintPrec _ _ Minimal = text "?"
  pPrintPrec _ _ (Apply ty) = text "$" <#> brackets (pPrint ty)
  pPrintPrec _ _ (Tag ty) = text "T" <#> brackets (pPrint ty)
  pPrintPrec _ _ (Skolem x) = text ("sk" ++ show x)

instance (Ord fun, Typeable fun, PrettyTerm fun) => PrettyTerm (Extended fun) where
  termStyle (Function f _) = termStyle f
  termStyle (Apply _) = infixStyle 0
  termStyle (Tag _) = uncurried
  termStyle _ = curried

instance (Sized fun, Pretty fun, PrettyTerm fun, Ord fun, Typeable fun) => Ordered (Extended fun) where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn
  lessEqSkolem = KBO.lessEqSkolem

newtype Pruner fun m a =
  Pruner (ReaderT (Twee.Config (Extended fun)) (StateT (Set (Twee.Fun (Extended fun)), State (Extended fun)) m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner . lift . lift

run :: (Typeable fun, Ord fun, Sized fun, Monad m) => Config -> Pruner fun m a -> m a
run Config{..} (Pruner x) =
  evalStateT (runReaderT x config) (Set.empty, initialState config)
  where
    config =
      defaultConfig {
        Twee.cfg_accept_term = Just (\t -> size t <= cfg_max_term_size),
        Twee.cfg_max_cp_depth = cfg_max_cp_depth }

instance (Labelled fun, Sized fun) => Sized (Twee.Term fun) where
  size (Twee.Var _) = 1
  size (Twee.App f ts) =
    size (Twee.fun_value f) + sum (map size (Twee.unpack ts))

instance KBO.Weighted (Extended fun) where
  argWeight _ = 1

type Norm fun = Twee.Term (Extended fun)

instance (Typed fun, Ord fun, Typeable fun, PrettyTerm fun, Sized fun, Monad m) =>
  MonadPruner (Term fun) (Norm fun) (Pruner fun m) where
  normaliser = Pruner $ do
    (_, state) <- lift get
    return $ \t ->
      let u = normaliseTwee state t in
      u
      -- traceShow (text "normalise:" <+> pPrint t <+> text "->" <+> pPrint u) u

  add ([] :=>: t :=: u) = Pruner $ do
    (funs, state) <- lift get
    config <- ask
    let (t' :=: u') = canonicalise (t :=: u)
    if not (null (Set.intersection (normalFormsTwee state t') (normalFormsTwee state u'))) then
      return False
    else do
      let (!funs', !state') = addTwee config t u funs state
      lift $ put (funs', state')
      return True

  add _ =
    return True
    --error "twee pruner doesn't support non-unit equalities"

normaliseTwee :: (Typed fun, Ord fun, Typeable fun, PrettyTerm fun, Sized fun) =>
  State (Extended fun) -> Term fun -> Norm fun
normaliseTwee state t =
  result u (normaliseTerm state u)
  where
    u = simplifyTerm state (skolemise t)

normalFormsTwee :: (Typed fun, Ord fun, Typeable fun, PrettyTerm fun, Sized fun) =>
  State (Extended fun) -> Term fun -> Set (Norm fun)
normalFormsTwee state t =
  Set.fromList . Map.elems $ Map.mapWithKey result (normalForms state (skolemise t))

addTwee :: (Typed fun, Ord fun, Typeable fun, PrettyTerm fun, Sized fun) =>
  Twee.Config (Extended fun) -> Term fun -> Term fun ->
  Set (Twee.Fun (Extended fun)) -> State (Extended fun) ->
  (Set (Twee.Fun (Extended fun)), State (Extended fun))
addTwee config t0 u0 funs state =
  addWithAxioms process (funs, state) (axiom (Twee.builder t) (Twee.builder u))
  where
    t = toTwee t0
    u = toTwee u0

    process = {-dump . -} interreduce config . completePure config
{-
    dump !state =
      unsafePerformIO $ do
        putStrLn "Rules:"
        forM_ (IntMap.toList (Twee.st_active_set state)) $ \(i, active) ->
          putStrLn ("  " ++ show i ++ ". " ++ prettyShow (Twee.active_rule active))
        return $! state
-}

    addWithAxioms proc (funs, state) ax@Axiom{axiom_eqn = t Twee.:=: u} =
      (funs'', proc $ addAxiom config (proc state'') ax)
      where
        funs' =
          Set.fromList (Twee.funs t ++ Twee.funs u) `Set.difference` funs
        (funs'', state') =
          foldl' (addWithAxioms id)
            (funs `Set.union` funs', state)
            (concatMap axioms (map Twee.fun_value (Set.toList funs')))
        state'' = proc state'

axiom :: (Typed fun, Ord fun, Typeable fun, PrettyTerm fun) =>
  Twee.Builder (Extended fun) -> Twee.Builder (Extended fun) -> Axiom (Extended fun)
axiom t0 u0 = Axiom 0 (prettyShow (t :=: u)) (t Twee.:=: u)
  where
    t = Twee.build t0
    u = Twee.build u0

axioms :: (Typed fun, Ord fun, Typeable fun, PrettyTerm fun) =>
  Extended fun -> [Axiom (Extended fun)]
axioms (Function f n) =
  [ axiom (tag (typeDrop n (typ f)) (papp f n)) (papp f n) ] ++
  [ axiom (papp' f n i (tag ty (var i))) (papp f n)
  | (i, ty) <- zip [0..n-1] (typeArgs (typ f)) ] ++
  [ axiom (app (typeDrop n (typ f)) (papp f n) (var n)) (papp f (n+1))
  | n < typeArity (typ f) ]
axioms (Apply ty) =
  [axiom (tag res expr) expr,
   axiom (app ty (tag ty (var 0)) (var 1)) expr,
   axiom (app ty (var 0) (tag arg (var 1))) expr] 
  where
    expr = app ty (var 0) (var 1)
    Just (arg, res) = unpackArrow ty
axioms _ = []

fun :: (Typed f, Ord f, Typeable f) => f -> Twee.Builder (Extended f)
fun f = Twee.con (Twee.fun (Function f 0))

papp :: (Typed f, Ord f, Typeable f) => f -> Int -> Twee.Builder (Extended f)
papp f n = Twee.app (Twee.fun (Function f n)) (map var [0..n-1])

papp' :: (Typed f, Ord f, Typeable f) => f -> Int -> Int -> Twee.Builder (Extended f) -> Twee.Builder (Extended f)
papp' f n i t = Twee.app (Twee.fun (Function f n)) (map var [0..i-1] ++ [t] ++ map var [i+1..n-1])

skolem :: (Typed f, Ord f, Typeable f) => Int -> Twee.Builder (Extended f)
skolem x = Twee.con (Twee.fun (Skolem x))

var :: Int -> Twee.Builder f
var = Twee.var . Twee.V

tag :: (Typed f, Ord f, Typeable f) =>
  Type -> Twee.Builder (Extended f) -> Twee.Builder (Extended f)
tag ty x = Twee.app (Twee.fun (Tag ty)) x

app ::
  (Typed f, Ord f, Typeable f) =>
  Type -> Twee.Builder (Extended f) -> Twee.Builder (Extended f) -> Twee.Builder (Extended f)
app ty x y = Twee.app (Twee.fun (Apply ty)) (Twee.builder x `mappend` Twee.builder y)

toTwee :: (Typed f, Ord f, Typeable f) =>
  Term f -> Twee.Term (Extended f)
toTwee = toTweeWith var

skolemise :: (Typed f, Ord f, Typeable f) =>
  Term f -> Twee.Term (Extended f)
skolemise = toTweeWith skolem

{-# INLINE toTweeWith #-}
toTweeWith :: (Typed f, Ord f, Typeable f) =>
  (Int -> Twee.Builder (Extended f)) ->
  Term f -> Twee.Term (Extended f)
toTweeWith var = Twee.build . tt
  where
    tt t = tag (typ t) (tt1 t)
    tt1 (Var x) = var (var_id x)
    tt1 (Fun f) = fun f
    tt1 (t :$: u) = app (typ t) (tt t) (tt u)
