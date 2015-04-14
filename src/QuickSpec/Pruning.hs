{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, GADTs #-}
module QuickSpec.Pruning where

#include "errors.h"
import QuickSpec.Base
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
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Rewriting.Substitution.Type
import Data.Maybe
import Control.Monad
import Control.Applicative
import Data.Ord

data AxiomMode = Normal | WithoutConsequences

class Pruner s where
  emptyPruner   :: Signature -> s
  untypedRep    :: [PropOf PruningTerm] -> PruningTerm -> StateT s IO (Maybe PruningTerm)
  untypedAxiom  :: AxiomMode -> PropOf PruningTerm -> StateT s IO ()
  pruningReport :: s -> String
  pruningReport _ = ""

instance Pruner [PropOf PruningTerm] where
  emptyPruner _       = []
  untypedRep _ _      = return Nothing
  untypedAxiom _ prop = modify (prop:)

newtype PrunerM s a =
  PrunerM {
    unPrunerM :: RulesT PruningConstant (ReaderT [Type] (StateT s IO)) a }
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
    fun@(TermConstant con _) <- event
    let arity = funArity con
    execute $ do
      let ty = typ (Fun con (replicate arity (undefined :: Term)))
          t = Fun fun (take arity (map Var [0..]))
          args = take arity (typeArgs (typ con))
      generate (HasType ty)
      unPrunerM $ liftPruner $
        untypedAxiom Normal ([] :=>: Fun (HasType ty) [t] :=: t)
      forM_ (zip [0..] args) $ \(i, ty) -> do
        let vs = map (Var . PruningVariable) [0..arity-1]
            tm f = Fun fun (take i vs ++ [f (vs !! i)] ++ drop (i+1) vs)
        generate (HasType ty)
        unPrunerM $ liftPruner $
          untypedAxiom Normal ([] :=>: tm (\t -> Fun (HasType ty) [t]) :=: tm id)

  rule $ do
    idFun@(TermConstant idCon idTy) <- event
    require (isId idCon)
    fun@(TermConstant con ty) <- event
    require (idTy == Fun Arrow [ty, ty])
    execute $ do
      let fun' = TermConstant con { conArity = arity + 1 } ty
          arity = conArity con
          x:xs = map (Var . PruningVariable) [0..arity]
      unPrunerM $ liftPruner $
        untypedAxiom Normal ([] :=>: Fun idFun [Fun fun xs, x] :=: Fun fun' (xs ++ [x]))

  rule $ do
    fun@(HasType ty) <- event
    execute $
      unPrunerM $ liftPruner $
        untypedAxiom Normal ([] :=>: Fun fun [Fun fun [Var 0]] :=: Fun fun [Var 0])

axiom :: Pruner s => AxiomMode -> Prop -> PrunerM s ()
axiom mode p = do
  univ <- askUniv
  when (null (instances univ p)) $
    ERROR . show . sep $
      [text "No instances in",
       nest 2 (pretty univ),
       text "for",
       nest 2 (pretty p <+> text "::" <+> pretty (propType p)),
       text "under",
       nest 2 (pretty [ pretty t <+> text "::" <+> pretty (typ t) | t <- usort (terms p >>= subterms) ])]
  sequence_
    [ do sequence_ [ PrunerM (generate fun) | fun <- usort (funs p') ]
         liftPruner (untypedAxiom mode p')
    | p' <- map toAxiom (instances univ p) ]

toAxiom :: Prop -> PropOf PruningTerm
toAxiom = normaliseProp . guardNakedVariables . fmap toPruningConstant
  where
    guardNakedVariables (lhs :=>: t :=: u) =
      lhs :=>: guardTerm t :=: guardTerm u
    guardNakedVariables prop = prop
    guardTerm (Var x) = Fun (HasType (typ x)) [Var x]
    guardTerm t = t

toGoal :: Prop -> PropOf PruningTerm
toGoal = fmap toGoalTerm

toGoalTerm :: Term -> PruningTerm
toGoalTerm = skolemise . guardNaked . toPruningConstant
  where
    guardNaked (Var x) = Fun (HasType (typ x)) [Var x]
    guardNaked t = t

toPruningConstant :: Term -> Tm PruningConstant Variable
toPruningConstant = mapTerm f id
  where
    f fun = TermConstant fun (typ fun)

skolemise :: Tm PruningConstant Variable -> PruningTerm
skolemise (Fun f xs) = Fun f (map skolemise xs)
skolemise (Var x) = Fun (SkolemVariable (PruningVariable (number x))) []

normaliseVars t = rename (\x -> fromMaybe __ (Map.lookup x m)) t
  where
    m = Map.fromList (zip (usort (vars t)) [0..])

normaliseProp prop =
  fmap (rename (\x -> fromMaybe __ (Map.lookup x m))) prop
  where
    m = Map.fromList (zip (usort (vars prop)) [0..])

instances :: [Type] -> Prop -> [Prop]
instances univ prop =
  [ fmap (typeSubst (evalSubst sub)) prop
  | sub <- map fromMap cs ]
  where
    cs =
      foldr intersection [Map.empty]
        (map (constrain univ)
          (usort
            (concatMap subterms
              (terms prop))))

intersection :: [Map TyVar Type] -> [Map TyVar Type] -> [Map TyVar Type]
ms1 `intersection` ms2 = usort [ Map.union m1 m2 | m1 <- ms1, m2 <- ms2, ok m1 m2 ]
  where
    ok m1 m2 = and [ Map.lookup x m1 == Map.lookup x m2 | x <- Map.keys (Map.intersection m1 m2) ]

constrain :: [Type] -> Term -> [Map TyVar Type]
constrain univ t =
  usort [ toMap sub | u <- univ, Just sub <- [match (typ t) u] ]

rep :: Pruner s => Term -> PrunerM s (Maybe Term)
rep t = liftM (liftM fromPruningTerm) $ do
  let u = toGoalTerm t
  sequence_ [ PrunerM (generate fun) | fun@(TermConstant con _) <- funs u ]
  liftPruner (untypedRep [] u)

type PruningTerm = Tm PruningConstant PruningVariable

data PruningConstant
  = SkolemVariable PruningVariable
    -- The type of a TermConstant is always the same as the underlying
    -- constant's type, it's only included here so that it's counted
    -- in the Ord instance
  | TermConstant Constant Type
    -- Since HasType has weight 0, it must be the biggest constant.
  | HasType Type
  deriving (Eq, Show)

instance Minimal PruningConstant where
  minimal = SkolemVariable (PruningVariable 0)

instance Ord PruningConstant where
  compare = comparing f
    where
      f (SkolemVariable x)    = Left x
      f (TermConstant x ty) = Right (Left (x, ty))
      f (HasType ty)          = Right (Right ty)

-- We have the property that size (skolemise t) == size t,
-- which is useful because we use the size to decide whether
-- to keep a critical pair.
instance Sized PruningConstant where
  funSize (TermConstant c _) = funSize c
  funSize (SkolemVariable _) = 1
  funSize (HasType _) = 0
  funArity (TermConstant c _) = funArity c
  funArity (SkolemVariable _) = 0
  funArity (HasType _) = 1

newtype PruningVariable = PruningVariable Int deriving (Eq, Ord, Num, Enum, Show, Numbered)

instance Pretty PruningConstant where
  pretty (TermConstant x _) = pretty x
  pretty (SkolemVariable x) = text "s" <> pretty x
  pretty (HasType ty) = text "@" <> prettyPrec 11 ty
instance PrettyTerm PruningConstant where
  termStyle (TermConstant x _) = termStyle x
  termStyle _ = Curried

instance Pretty PruningVariable where
  pretty (PruningVariable x) = text "v" <> pretty x

fromPruningTerm :: PruningTerm -> Term
fromPruningTerm t =
  fromPruningTermWith n t
  where
    n = maximum (0:[1+n | SkolemVariable (PruningVariable n) <- funs t])

fromPruningTermWith :: Int -> PruningTerm -> Term
fromPruningTermWith n (Fun (TermConstant fun _) xs) =
  Fun fun (zipWith (fromPruningTermWithType n) (typeArgs (typ fun)) xs)
fromPruningTermWith n (Fun (HasType ty) [t]) = fromPruningTermWithType n ty t
fromPruningTermWith _ _ = ERROR "ill-typed term?"

fromPruningTermWithType :: Int -> Type -> PruningTerm -> Term
fromPruningTermWithType m ty (Var (PruningVariable n)) = Var (Variable (m+n) ty)
fromPruningTermWithType _ ty (Fun (SkolemVariable (PruningVariable n)) []) = Var (Variable n ty)
fromPruningTermWithType n _  t = fromPruningTermWith n t
