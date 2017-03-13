{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, GADTs #-}
module QuickSpec.Pruning where

#include "errors.h"
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Utils
import QuickSpec.Signature hiding (instances)
import QuickSpec.Prop
import QuickSpec.Rules
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import GHC.Stack
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Maybe
import Control.Monad
import Control.Applicative
import Data.Ord
import Twee.Base
import qualified Twee.KBO as KBO
import qualified Twee.Label as Label

instance Label.Labelled (Type, Var) where
  cache = typedVarCache

{-# NOINLINE typedVarCache #-}
typedVarCache :: Label.Cache (Type, Var)
typedVarCache = Label.mkCache

data AxiomMode = Normal | WithoutConsequences
type PruningConstant = Extended Constant
type PruningTerm = Term PruningConstant
type PruningProp = PropOf PruningTerm

instance Ordered PruningConstant where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn

class Pruner s where
  emptyPruner   :: Signature -> s
  untypedRep    :: [PruningProp] -> PruningTerm -> StateT s IO (Maybe PruningTerm)
  untypedAxiom  :: AxiomMode -> PruningProp -> StateT s IO ()
  pruningReport :: s -> String
  pruningReport _ = ""

instance Pruner [PruningProp] where
  emptyPruner _       = []
  untypedRep _ _      = return Nothing
  untypedAxiom _ prop = modify (prop:)

newtype PrunerM s a =
  PrunerM {
    unPrunerM :: RulesT Constant (ReaderT [Type] (StateT s IO)) a }
  deriving (Monad, MonadIO, Functor, Applicative)

askUniv :: PrunerM s [Type]
askUniv = PrunerM (lift ask)

liftPruner :: Pruner s => StateT s IO a -> PrunerM s a
liftPruner m = PrunerM (lift (lift m))

evalPruner :: Pruner s => Signature -> s -> PrunerM s a -> IO a
evalPruner sig theory m = liftM fst (runPruner sig theory m)

runPruner :: Pruner s => Signature -> s -> PrunerM s a -> IO (a, s)
runPruner sig theory m =
  runStateT (runReaderT (runRulesT (unPrunerM m')) (Set.toList (typeUniverse sig))) theory
  where
    m' = createRules >> mapM_ (axiom Normal) (background sig) >> m

createRules :: Pruner s => PrunerM s ()
createRules = PrunerM $ do
  rule $ do
    con <- event
    let ar = arity con
    execute $ do
      let ty = typ (app con (replicate ar (build (var (MkVar 0)) :: Term Constant)))
          t = app (Function con) (take ar (map (build . var . MkVar) [0..]))
          args = take ar (typeArgs (typ con))
      generate (Id ty)
      unPrunerM $ liftPruner $
        untypedAxiom Normal ([] :=>: app (Function (Id ty)) [t] :=: t)
      forM_ (zip [0..] args) $ \(i, ty) -> do
        let vs = map (build . var . MkVar) [0..ar-1]
            tm f = app (Function con) (take i vs ++ [f (vs !! i)] ++ drop (i+1) vs)
        generate (Id ty)
        unPrunerM $ liftPruner $
          untypedAxiom Normal ([] :=>: tm (\t -> app (Function (Id ty)) [t]) :=: tm id)
      unPrunerM $ liftPruner $
        let u = app con (take ar (map (build . var . MkVar) [0..]))
            x = build (fun (toFun (Id (head (typeArgs (typ u) ++ [typeOf ()])))) [var (MkVar ar)]) in
        case tryApply' u x of
          Nothing -> return ()
          Just v ->
            untypedAxiom Normal ([] :=>: build (extended (singleton v)) :=: app (Function (Apply ty)) [t, build (var (MkVar ar))])

axiom :: (HasCallStack, Pruner s) => AxiomMode -> Prop -> PrunerM s ()
axiom mode p = do
  univ <- askUniv
  when (null (instances univ p)) $
    ERROR(show (sep
      [text "No instances in",
       nest 2 (pPrint univ),
       text "for",
       nest 2 (pPrint p <+> text "::" <+> pPrint (propType p)),
       text "under",
       nest 2 (pPrint [ pPrint t <+> text "::" <+> pPrint (typ t) | t <- filter isFun (usort (terms p >>= termListToList >>= subterms)) ])]))
  sequence_
    [ do sequence_ [ PrunerM (generate (fromFun fun)) | fun <- usort (funs p') ]
         liftPruner (untypedAxiom mode (toPruner p'))
    | p' <- instances univ p ]

unsafeAxiom :: (HasCallStack, Pruner s) => AxiomMode -> Prop -> PrunerM s ()
unsafeAxiom mode p = do
  univ <- askUniv
  sequence_
    [ do sequence_ [ PrunerM (generate (fromFun fun)) | fun <- usort (funs p') ]
         liftPruner (untypedAxiom mode (toPruner p'))
    | p' <- instances univ p ]

toGoal :: Prop -> PruningProp
toGoal = fmap (build . subst (con . skolem)) . toPruner

{-# INLINE toPruner #-}
toPruner :: Prop -> PruningProp
toPruner = fmap (build . aux . singleton)
  where
    aux Empty = mempty
    aux (Cons (App (Id ty) [Var x]) ts) =
      fun (toFun (Function (Id ty))) (var (MkVar (Label.label (ty, x)))) `mappend` aux ts
    aux (Cons (Fun f ts) us) = fun (toFun (Function (fromFun f))) (aux ts) `mappend` aux us
    aux (Cons (Var x) ts) = var x `mappend` aux ts

instances :: [Type] -> Prop -> [Prop]
instances univ prop =
  [ fmap (typeSubst (\x -> Map.findWithDefault __ x sub)) prop
  | sub <- cs ]
  where
    cs =
      foldr intersection [Map.empty]
        (map (constrain univ)
          (filter (\x -> isFun x && not (isDictionary (typ x)))
            (usort (terms prop >>= termListToList >>= subterms))))

intersection :: [Map Var Type] -> [Map Var Type] -> [Map Var Type]
ms1 `intersection` ms2 = usort [ Map.union m1 m2 | m1 <- ms1, m2 <- ms2, ok m1 m2 ]
  where
    ok m1 m2 = and [ Map.lookup x m1 == Map.lookup x m2 | x <- Map.keys (Map.intersection m1 m2) ]

constrain :: [Type] -> Term Constant -> [Map Var Type]
constrain univ t =
  usort [ Map.fromList (listSubst sub) | u <- univ, Just sub <- [match (typ t) u] ]

-- | Normalises a term using the current rewrite rules
rep :: Pruner s => Term Constant -> PrunerM s (Maybe (Term Constant))
rep t = liftM (check . liftM (build . inferTypes . build . unextended . singleton)) $ do
  let u = build (subst (con . skolem) (build (extended (singleton t))))
  sequence_ [ PrunerM (generate (fromFun con)) | con <- funs t ]
  liftPruner (untypedRep [] u)
  where
    check (Just u) | t == u = Nothing
    check x = x

inferTypes :: Term Constant -> Builder Constant
inferTypes t = aux __ t
  where
    aux ty (Var x) = fun (toFun (Id ty)) (var x)
    aux ty t@(App (Id _) [Var _]) = builder t
    aux _ (Fun f ts) = fun f (zipWith aux tys (fromTermList ts))
      where
        tys = typeArgs (typ (fromFun f))
