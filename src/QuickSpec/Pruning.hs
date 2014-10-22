{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
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

class Pruner s where
  emptyPruner   :: s
  untypedRep    :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT s m (Maybe PruningTerm)
  untypedAxiom  :: Monad m => PropOf PruningTerm -> StateT s m ()
  untypedGoal   :: Monad m => PropOf PruningTerm -> StateT s m Bool

newtype PrunerT s m a =
  PrunerT {
    unPrunerT :: RulesT PruningConstant (ReaderT [Type] (StateT s m)) a }
  deriving (Monad, MonadIO, Functor, Applicative)
instance MonadTrans (PrunerT s) where
  lift = PrunerT . lift . lift . lift

askUniv :: Monad m => PrunerT s m [Type]
askUniv = PrunerT (lift ask)

liftPruner :: (Monad m, Pruner s) => StateT s m a -> PrunerT s m a
liftPruner m = PrunerT (lift (lift m))

runPruner :: (Monad m, Pruner s) => Signature -> PrunerT s m a -> m a
runPruner sig m =
  evalStateT (runReaderT (runRulesT (unPrunerT m')) (Set.toList (typeUniverse sig))) emptyPruner
  where
    m' = createRules >> mapM_ axiom (background sig) >> m

createRules :: (Monad m, Pruner s) => PrunerT s m ()
createRules = PrunerT $ do
  rule $ do
    fun@(TermConstant con _ arity) <- event
    execute $ do
      let ty = typ (Fun con (replicate arity (undefined :: Term)))
          t = Fun fun (take arity (map Var [0..]))
      unPrunerT $ liftPruner $
        untypedAxiom ([] :=>: Fun (HasType ty) [t] :=: t)

axiom :: (Pruner s, Monad m) => Prop -> PrunerT s m ()
axiom p = do
  univ <- askUniv
  sequence_
    [ do sequence_ [ PrunerT (generate fun) | fun <- usort (concatMap funs (propTerms p')) ]
         liftPruner (untypedAxiom p')
    | p' <- map toAxiom (instances univ p) ]

goal :: (Pruner s, Monad m) => Prop -> PrunerT s m Bool
goal p = do
  let p' = toGoal p
  sequence_ [ PrunerT (generate fun) | fun <- usort (concatMap funs (propTerms p')) ]
  liftPruner (untypedGoal p')

toAxiom :: Prop -> PropOf PruningTerm
toAxiom = normaliseProp . guardNakedVariables . fmap toPruningConstant
  where
    guardNakedVariables (lhs :=>: t :=: u) =
      lhs :=>: guardTerm t :=: guardTerm u
    guardNakedVariables prop = prop
    guardTerm (Var x) = Fun (HasType (typ x)) [Var x]
    guardTerm t = t

toGoal :: Prop -> PropOf PruningTerm
toGoal p = (axs ++ lhs p') :=>: rhs p'
  where
    p' = fmap (skolemise . toPruningConstant) p
    axs = [ skolemAxiom x | SkolemVariable x <- usort (concatMap funs (propTerms p')) ]

toGoalTerm :: Term -> ([Literal PruningTerm], PruningTerm)
toGoalTerm t = (axs, u)
  where
    u = skolemise (toPruningConstant t)
    axs = [ skolemAxiom x | SkolemVariable x <- usort (funs u) ]

toPruningConstant :: Term -> Tm PruningConstant Variable
toPruningConstant = mapTerm f id . withArity
  where
    f (fun, n) = TermConstant fun (typ fun) n

skolemise :: Tm PruningConstant Variable -> PruningTerm
skolemise (Fun f xs) = Fun f (map skolemise xs)
skolemise (Var x) = Fun (SkolemVariable x) []

skolemAxiom :: Variable -> Literal PruningTerm
skolemAxiom x =
  Fun (HasType (typ x)) [t] :=: t
  where
    t = Fun (SkolemVariable x) []

normaliseVars t = rename (\x -> fromMaybe __ (Map.lookup x m)) t
  where
    m = Map.fromList (zip (usort (vars t)) [0..])

normaliseProp prop =
  fmap (rename (\x -> fromMaybe __ (Map.lookup x m))) prop
  where
    m = Map.fromList (zip (usort (concatMap vars (propTerms prop))) [0..])

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
              (propTerms prop))))

intersection :: [Map TyVar Type] -> [Map TyVar Type] -> [Map TyVar Type]
ms1 `intersection` ms2 = usort [ Map.union m1 m2 | m1 <- ms1, m2 <- ms2, ok m1 m2 ]
  where
    ok m1 m2 = and [ Map.lookup x m1 == Map.lookup x m2 | x <- Map.keys (Map.intersection m1 m2) ]

constrain :: [Type] -> Term -> [Map TyVar Type]
constrain univ t =
  usort [ toMap sub | u <- univ, Just sub <- [match (typ t) u] ]

rep :: (Pruner s, Monad m) => Term -> PrunerT s m (Maybe Term)
rep t = liftM (liftM fromPruningTerm) (liftPruner (untypedRep (map unitProp axs) u))
  where
    (axs, u) = toGoalTerm t

type PruningTerm = Tm PruningConstant PruningVariable

data PruningConstant
  = TermConstant Constant Type Int
    -- The type is always the same as the constant's type,
    -- it's only included here so that it's counted in the Ord instance
  | SkolemVariable Variable
  | HasType Type
  deriving (Eq, Ord, Show)

newtype PruningVariable = PruningVariable Int deriving (Eq, Ord, Num, Enum, Show)

instance Pretty PruningConstant where
  pretty (TermConstant x _ _) = pretty x
  pretty (SkolemVariable x) = text "s" <> pretty x
  pretty (HasType ty) = text "@" <> pretty ty
instance PrettyTerm PruningConstant where

instance Pretty PruningVariable where
  pretty (PruningVariable x) = text "v" <> pretty x

fromPruningTerm :: PruningTerm -> Term
fromPruningTerm t =
  fromPruningTermWith n t
  where
    n = maximum (0:[1+n | SkolemVariable (Variable n _) <- funs t])

fromPruningTermWith :: Int -> PruningTerm -> Term
fromPruningTermWith n (Fun (TermConstant fun _ _) xs) =
  Fun fun (zipWith (fromPruningTermWithType n) (typeArgs (typ fun)) xs)
fromPruningTermWith n (Fun (HasType ty) [t]) = fromPruningTermWithType n ty t
fromPruningTermWith n (Fun (SkolemVariable x) []) = Var x
fromPruningTermWith _ _ = ERROR "ill-typed term?"

fromPruningTermWithType :: Int -> Type -> PruningTerm -> Term
fromPruningTermWithType m ty (Var (PruningVariable n)) = Var (Variable (m+n) ty)
fromPruningTermWithType n _  t = fromPruningTermWith n t
