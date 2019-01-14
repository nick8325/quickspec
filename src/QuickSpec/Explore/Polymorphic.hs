-- Theory exploration which handles polymorphism.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
module QuickSpec.Explore.Polymorphic(module QuickSpec.Explore.Polymorphic, Result(..), Universe(..)) where

import qualified QuickSpec.Explore.Schemas as Schemas
import QuickSpec.Explore.Schemas(Schemas, Result(..))
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Utils
import QuickSpec.Prop
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Lens.Light
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import qualified Twee.Base as Twee
import Control.Monad
import qualified Data.DList as DList

data Polymorphic testcase result fun norm =
  Polymorphic {
    pm_schemas :: Schemas testcase result (PolyFun fun) norm,
    pm_universe :: Universe }

data PolyFun fun =
  PolyFun { fun_original :: fun, fun_specialised :: fun }
  deriving (Eq, Ord)

instance Pretty fun => Pretty (PolyFun fun) where
  pPrint = pPrint . fun_specialised

instance PrettyTerm fun => PrettyTerm (PolyFun fun) where
  termStyle = termStyle . fun_specialised

-- The set of all types being explored
data Universe = Universe { univ_types :: Set Type }

makeLensAs ''Polymorphic
  [("pm_schemas", "schemas"),
   ("pm_universe", "univ")]

initialState ::
  (Type -> Bool) ->
  Universe ->
  (Term fun -> Bool) ->
  (Term fun -> testcase -> result) ->
  Polymorphic testcase result fun norm
initialState singleUse univ inst eval =
  Polymorphic {
    pm_schemas = Schemas.initialState singleUse (inst . fmap fun_specialised) (eval . fmap fun_specialised),
    pm_universe = univ }

polyFun :: Typed fun => fun -> PolyFun fun
polyFun x = PolyFun x (oneTypeVar x)

polyTerm :: Typed fun => Term fun -> Term (PolyFun fun)
polyTerm = oneTypeVar . fmap polyFun

instance Typed fun => Typed (PolyFun fun) where
  typ = typ . fun_specialised
  otherTypesDL = otherTypesDL . fun_specialised
  typeSubst_ _ x = x -- because it's supposed to be monomorphic

newtype PolyM testcase result fun norm m a = PolyM { unPolyM :: StateT (Polymorphic testcase result fun norm) m a }
  deriving (Functor, Applicative, Monad)

explore ::
  (PrettyTerm fun, Ord result, Ord norm, Typed fun, Ord fun, Apply (Term fun),
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m) =>
  Term fun ->
  StateT (Polymorphic testcase result fun norm) m (Result fun)
explore t = do
  univ <- access univ
  unless (t `usefulForUniverse` univ) $
    error ("Type " ++ prettyShow (typ t) ++ " not in universe for " ++ prettyShow t)
  if not (t `inUniverse` univ) then
    return (Accepted [])
   else do
    res <- exploreNoMGU t
    case res of
      Rejected{} -> return res
      Accepted{} -> do
        ress <- forM (typeInstances univ t) $ \u ->
          exploreNoMGU u
        return res { result_props = concatMap result_props (res:ress) }

exploreNoMGU ::
  (PrettyTerm fun, Ord result, Ord norm, Typed fun, Ord fun, Apply (Term fun),
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m) =>
  Term fun ->
  StateT (Polymorphic testcase result fun norm) m (Result fun)
exploreNoMGU t = do
  univ <- access univ
  if not (t `inUniverse` univ) then return (Rejected []) else do
    schemas1 <- access schemas
    (res, schemas2) <- unPolyM (runStateT (Schemas.explore (polyTerm t)) schemas1)
    schemas ~= schemas2
    return (mapProps (regeneralise . mapFun fun_original) res)
  where
    mapProps f (Accepted props) = Accepted (map f props)
    mapProps f (Rejected props) = Rejected (map f props)

instance (PrettyTerm fun, Ord fun, Typed fun, Apply (Term fun), MonadPruner (Term fun) norm m) =>
  MonadPruner (Term (PolyFun fun)) norm (PolyM testcase result fun norm m) where
  normaliser = PolyM $ do
    norm <- normaliser
    return (norm . fmap fun_specialised)
  add prop = PolyM $ do
    univ <- access univ
    let insts = typeInstances univ (canonicalise (regeneralise (mapFun fun_original prop)))
    or <$> mapM add insts

instance MonadTester testcase (Term fun) m =>
  MonadTester testcase (Term (PolyFun fun)) (PolyM testcase result fun norm m) where
  test prop = PolyM $ lift (test (mapFun fun_original prop))

-- Given a property which only contains one type variable,
-- add as much polymorphism to the property as possible.
-- e.g.    map (f :: a -> a) (xs++ys) = map f xs++map f ys
-- becomes map (f :: a -> b) (xs++ys) = map f xs++map f ys.
regeneralise :: (PrettyTerm fun, Typed fun, Apply (Term fun)) => Prop (Term fun) -> Prop (Term fun)
regeneralise =
  -- First replace each type variable occurrence with a fresh
  -- type variable (generalise), then unify type variables
  -- where necessary to preserve well-typedness (restrict).
  restrict . unPoly . generalise
  where
    generalise (lhs :=>: rhs) =
      polyApply (:=>:) (polyList (map genLit lhs)) (genLit rhs)
    genLit (t :=: u) = polyApply (:=:) (genTerm t) (genTerm u)
    genTerm (Var (V ty x)) =
      -- It's tempting to return Var (V typeVar x) here.
      -- But this is wrong!
      -- In the case of the type (), we get the law x == y :: (),
      -- which we must not generalise to x == y :: a.
      poly (Var (V (genType ty) x))
    genTerm (App f ts) =
      let
        -- Need to polymorphise all of ts together so that type variables which
        -- only occur in subterms of ts don't get unified
        (f', us) = unPoly (polyPair (poly f) (polyList (map genTerm ts)))
        Just ty = fmap unPoly (polyMgu (polyTyp (poly f')) (polyApply arrowType (poly (map typ us)) (poly typeVar)))
        tys = take (length us) (typeArgs ty)
        Just f'' = cast ty f'
        Just us' = sequence (zipWith cast tys us)
      in
        poly (App f'' us')

    genType = Twee.build . aux 0 . Twee.singleton
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
        vs = partitionBy skel (concatMap vars (terms prop >>= subterms))
        skel (V ty x) = V (oneTypeVar ty) x
    litCs (t :=: u) = [(typ t, typ u)]

typeInstancesList :: [Type] -> [Type] -> [Twee.Var -> Type]
typeInstancesList types prop =
  map eval
    (foldr intersection [Map.empty]
      (map constrain
        (usort prop)))
  where
    constrain t =
      usort [ Map.fromList (Twee.substToList sub) | u <- types, Just sub <- [Twee.match t u] ]
    eval sub x =
      Map.findWithDefault (error ("not found: " ++ prettyShow x)) x sub

typeInstances :: (Pretty a, PrettyTerm fun, Symbolic fun a, Ord fun, Typed fun, Typed a) => Universe -> a -> [a]
typeInstances Universe{..} prop =
  [ typeSubst sub prop
  | sub <- typeInstancesList (Set.toList univ_types) (map typ (DList.toList (termsDL prop) >>= subterms)) ]

intersection :: [Map Twee.Var Type] -> [Map Twee.Var Type] -> [Map Twee.Var Type]
ms1 `intersection` ms2 = usort [ Map.union m1 m2 | m1 <- ms1, m2 <- ms2, ok m1 m2 ]
  where
    ok m1 m2 = and [ Map.lookup x m1 == Map.lookup x m2 | x <- Map.keys (Map.intersection m1 m2) ]

universe :: Typed a => [a] -> Universe
universe xs = Universe (Set.fromList univ)
  where
    -- Types of all functions
    types = usort $ typeVar:map typ xs

    -- Take the argument and result type of every function.
    univBase = usort $ concatMap components types

    -- Add partially-applied functions, if they can be used to
    -- fill in a higher-order argument.
    univHo = usort $ concatMap addHo univBase
      where
        addHo ty =
          ty:
          [ typeSubst sub ho
          | fun <- types,
            ho <- arrows fun,
            sub <- typeInstancesList univBase (components fun) ]
  
    -- Add antiunifiers of all pairs of types, so that each equation
    -- has a most general type
    univ = usort $ oneTypeVar $ fixpoint antiunifiers univHo
      where
        antiunifiers tys =
          usort $ map (unPoly . poly) $
            tys ++ [antiunify ty1 ty2 | ty1 <- tys, ty2 <- tys]

    components ty =
      case unpackArrow ty of
        Nothing -> [ty]
        Just (ty1, ty2) -> components ty1 ++ components ty2

    arrows ty =
      concatMap arrows1 (typeArgs ty)
      where
        arrows1 ty
          | isArrowType ty =
            ty:concatMap arrows1 (typeArgs ty)
          | otherwise =
            []
 
inUniverse :: Typed fun => Term fun -> Universe -> Bool
t `inUniverse` Universe{..} =
  and [oneTypeVar (typ u) `Set.member` univ_types | u <- subterms t]

usefulForUniverse :: Typed fun => Term fun -> Universe -> Bool
t `usefulForUniverse` Universe{..} =
  and [oneTypeVar (typ u) `Set.member` univ_types | u <- properSubterms t] &&
  oneTypeVar (typeRes (typ t)) `Set.member` univ_types
