-- Theory exploration which handles polymorphism.
{-# LANGUAGE TemplateHaskell, FlexibleContexts, GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses, BangPatterns, UndecidableInstances, RankNTypes #-}
module QuickSpec.Explore.Polymorphic(module QuickSpec.Explore.Polymorphic, Result(..)) where

import qualified QuickSpec.Explore.Schemas as Schemas
import QuickSpec.Explore.Schemas(Schemas, Result(..))
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Utils
import QuickSpec.Terminal
import QuickSpec.Prop
import QuickSpec.Pruning.Background(Background(..))
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Lens.Light
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import qualified Twee.Base as Twee
import Control.Monad
import Data.Maybe
import Data.Reflection
import Test.QuickCheck(Arbitrary, CoArbitrary)
import Data.Proxy
import Debug.Trace

data Polymorphic testcase result fun =
  Polymorphic {
    pm_schemas :: Schemas testcase result (Specialised fun),
    pm_unifiable :: Map (Poly Type) ([Poly Type], [(Poly Type, Poly Type)]),
    pm_accepted :: Map (Poly Type) [Term fun],
    pm_universe :: Set Type }

newtype Specialised fun =
  Spec { spec_fun :: fun }
  deriving (Eq, Ord, Background, Pretty, PrettyTerm, Sized, Arity)

makeLensAs ''Polymorphic
  [("pm_schemas", "schemas"),
   ("pm_unifiable", "unifiable"),
   ("pm_accepted", "accepted"),
   ("pm_universe", "universe")]

initialState ::
  (Given DefaultType, Typed fun) =>
  [Type] -> 
  (Term fun -> Bool) ->
  (Term fun -> testcase -> result) ->
  Polymorphic testcase result fun
initialState univ inst eval =
  Polymorphic {
    pm_schemas = Schemas.initialState (inst . fmap spec_fun) (eval . defaultTypes . fmap spec_fun),
    pm_unifiable = Map.empty,
    pm_accepted = Map.empty,
    pm_universe = Set.fromList univ }

withDefaultType :: Type -> (Given DefaultType => a) -> a
withDefaultType ty = give (DefaultType ty)

explore ::
  (Given DefaultType, Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun ->
  StateT (Polymorphic testcase result fun) m (Result fun)
explore t = do
  univ <- access universe
  when (oneTypeVar (typ t) `notElem` univ) $
    error ("Type " ++ prettyShow (typ t) ++ " not in universe for " ++ prettyShow t)
  res <- exploreNoMGU t
  case res of
    Accepted{} -> do
      let ty = polyTyp (poly t)
      addPolyType ty
      
      unif <- access unifiable
      let (here, there) = Map.findWithDefault undefined ty unif
      acc <- access accepted
      ress1 <-
        forM here (\mgu ->
          exploreNoMGU (t `at` mgu))
      ress2 <-
        concat <$>
        forM there (\(ty', mgu) ->
          forM (Map.findWithDefault undefined ty' acc) (\u ->
            exploreNoMGU (u `at` mgu)))
        
      accepted %= Map.insertWith (++) ty [t]
      return res { result_props = concatMap result_props (res:ress1 ++ ress2) }
    Rejected{} ->
      return res
  where
    t `at` ty =
      fromMaybe undefined (cast (unPoly ty) t)

exploreNoMGU ::
  (Given DefaultType, Ord result, Sized fun, Typed fun, Ord fun, PrettyTerm fun,
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) m) =>
  Term fun ->
  StateT (Polymorphic testcase result fun) m (Result fun)
exploreNoMGU t = do
  --traceM ("exploring " ++ prettyShow t ++ " :: " ++ prettyShow (typ t))
  univ <- access universe
  schemas1 <- access schemas
  (res, schemas2) <-
    flip runReaderT (Set.toList univ) $ runPruner $ runTester $
    -- XXX but surely we also have to oneTypeVar the variables?
    runStateT (Schemas.explore (fmap Spec t)) schemas1
  schemas ~= schemas2
  return res { result_props = map regeneralise (result_props res) }

addPolyType :: Monad m => Poly Type -> StateT (Polymorphic testcase result fun) m ()
addPolyType ty = do
  unif <- access unifiable
  univ <- access universe
  unless (ty `Map.member` unif) $ do
    let
      tys = [(ty', mgu) | ty' <- Map.keys unif, Just mgu <- [polyMgu ty ty']]
      ok ty mgu = oneTypeVar ty /= mgu && unPoly mgu `Set.member` univ
      here = [mgu | (_, mgu) <- tys, ok mgu ty]
      there = [(ty', mgu) | (ty', mgu) <- tys, ok mgu ty']
    key ty # unifiable ~= Just (here, there)
    forM_ there $ \(ty', sub) ->
      sndLens # keyDefault ty' undefined # unifiable %= (there ++)

newtype Pruner fun m a = Pruner { runPruner :: ReaderT [Type] m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadTester testcase result, MonadTerminal)

instance (Given DefaultType, PrettyTerm fun, Ord fun, Typed fun, MonadPruner (Term fun) m) =>
  MonadPruner (Term (Specialised fun)) (Pruner fun m) where
  normaliser =
    Pruner $ do
      norm <- normaliser
      return (fmap Spec . norm . fmap spec_fun)
  add prop = Pruner $ do
    univ <- ask
    let insts = typeInstances univ (regeneralise prop)
    mapM_ add insts

newtype Tester fun m a = Tester { runTester :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadPruner term, MonadTerminal)

instance MonadTrans (Tester fun) where
  lift = Tester

instance (Given DefaultType, Typed fun, MonadTester testcase (Term fun) m) =>
  MonadTester testcase (Term (Specialised fun)) (Tester fun m) where
  test prop = lift (test (defaultTypes (mapFun spec_fun prop)))

newtype DefaultType = DefaultType Type
newtype Abstract a = Abstract a
  deriving (Eq, Ord, Arbitrary, CoArbitrary)

defaultTypes :: (Given DefaultType, Typed a) => a -> a
defaultTypes = typeSubst (const (Twee.build (Twee.app (Twee.fun tc) ty)))
  where
    DefaultType ty = given
    tc = tyCon (Proxy :: Proxy Abstract)

instance (Given DefaultType, Typed fun) => Typed (Specialised fun) where
  typ = defaultTypes . typ . spec_fun
  otherTypesDL = fmap defaultTypes . otherTypesDL . spec_fun
  typeSubst_ _ fun = fun -- typ fun is ground

-- Given a property which only contains one type variable,
-- add as much polymorphism to the property as possible.
-- e.g.    map (f :: a -> a) (xs++ys) = map f xs++map f ys
-- becomes map (f :: a -> b) (xs++ys) = map f xs++map f ys.
regeneralise :: Typed fun => Prop (Term (Specialised fun)) -> Prop (Term fun)
regeneralise =
  -- First replace each type variable occurrence with a fresh
  -- type variable (generalise), then unify type variables
  -- where necessary to preserve well-typedness (restrict).
  restrict . unPoly . generalise . canonicalise . mapFun spec_fun
  where
    generalise (lhs :=>: rhs) =
      polyApply (:=>:) (polyList (map genLit lhs)) (genLit rhs)
    genLit (t :=: u) = polyApply (:=:) (genTerm t) (genTerm u)
    genTerm (Var (V ty x)) =
      polyMap (\ty -> Var (V ty x)) (genType ty)
    genTerm (App f ts) =
      polyApply App (genCon f) (polyList (map genTerm ts))
    genCon f = poly f

    genTyped :: Typed a => Type -> a -> a
    genTyped ty x =
      let
        (ty', x') = unPoly (polyPair (genType ty) (poly x))
        Just sub = Twee.unify ty' (typ x')
      in typeSubst sub x'

    genType = poly . Twee.build . aux 0 . Twee.singleton
      where
        aux !_ Twee.Empty = mempty
        aux n (Twee.Cons (Twee.Var _) ts) =
          Twee.var (Twee.V n) `mappend` aux (n+1) ts
        aux n (Twee.Cons (Twee.App f ts) us) =
          Twee.app f (aux n ts) `mappend`
          aux (n+Twee.lenList ts) us

    restrict prop = typeSubst sub prop
      where
        Just sub = Twee.unifyList (Twee.buildList (map fst cs)) (Twee.buildList (map snd cs))
        cs = [(var_ty x, var_ty y) | x:xs <- vs, y <- xs] ++ concatMap litCs (lhs prop) ++ litCs (rhs prop)
        -- Two variables that were equal before generalisation must have the
        -- same type afterwards
        vs = partitionBy skel (concatMap vars (terms prop))
        skel (V ty x) = V (oneTypeVar ty) x
    litCs (t :=: u) = [(typ t, typ u)] ++ termCs t ++ termCs u
    termCs Var{} = []
    termCs t@(App f ts) = [(typ f, arrowType (map typ ts) (typ t))] ++ concatMap termCs ts

typeInstances :: (Ord fun, Typed fun) => [Type] -> Prop (Term fun) -> [Prop (Term fun)]
typeInstances univ prop =
  [ fmap (typeSubst (\x -> Map.findWithDefault undefined x sub)) prop
  | sub <- cs ]
  where
    cs =
      foldr intersection [Map.empty]
        (map constrain
          (filter (\x -> isApp x)
            (usort (terms prop >>= subterms))))

    constrain t =
      usort [ Map.fromList (Twee.substToList sub) | u <- univ, Just sub <- [Twee.match (typ t) u] ]

intersection :: [Map Twee.Var Type] -> [Map Twee.Var Type] -> [Map Twee.Var Type]
ms1 `intersection` ms2 = usort [ Map.union m1 m2 | m1 <- ms1, m2 <- ms2, ok m1 m2 ]
  where
    ok m1 m2 = and [ Map.lookup x m1 == Map.lookup x m2 | x <- Map.keys (Map.intersection m1 m2) ]
