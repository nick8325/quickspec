-- Theory exploration which handles polymorphism.
{-# LANGUAGE TemplateHaskell, FlexibleContexts, GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses, BangPatterns, UndecidableInstances, RankNTypes, GADTs #-}
module QuickSpec.Explore.Polymorphic(module QuickSpec.Explore.Polymorphic, Result(..)) where

import qualified QuickSpec.Explore.Schemas as Schemas
import QuickSpec.Explore.Schemas(Schemas, Result(..), Schematic(..))
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
import qualified Twee.Base as Twee

data Polymorphic testcase result schema norm =
  Polymorphic {
    pm_schemas :: Schemas testcase result (PolySchema schema) norm,
    pm_unifiable :: Map (Poly Type) ([Poly Type], [(Poly Type, Poly Type)]),
    pm_accepted :: Map (Poly Type) (Set schema),
    pm_universe :: Universe }

data PolySchema schema =
  PolySchema { polySchema :: schema, monoSchema :: schema }
  deriving (Eq, Ord)

newtype Universe = Universe (Set Type)

makeLensAs ''Polymorphic
  [("pm_schemas", "schemas"),
   ("pm_unifiable", "unifiable"),
   ("pm_accepted", "accepted"),
   ("pm_universe", "univ")]

initialState ::
  Universe ->
  (schema -> Bool) ->
  (schema -> testcase -> result) ->
  Polymorphic testcase result schema norm
initialState univ inst eval =
  Polymorphic {
    pm_schemas = Schemas.initialState (inst . monoSchema) (eval . monoSchema),
    pm_unifiable = Map.empty,
    pm_accepted = Map.empty,
    pm_universe = univ }

makeSchema :: Typed schema => schema -> PolySchema schema
makeSchema x = PolySchema x (oneTypeVar x)

instance (Typed schema, Symbolic fun schema) => Symbolic fun (PolySchema schema) where
  termsDL = termsDL . polySchema
  subst sub = makeSchema . subst sub . polySchema

instance (Typed schema, Schematic fun schema) => Schematic fun (PolySchema schema) where
  mostGeneralWith f = makeSchema . mostGeneralWith (f . oneTypeVar) . polySchema

instance Typed schema => Typed (PolySchema schema) where
  typ = typ . monoSchema
  otherTypesDL = otherTypesDL . monoSchema
  typeSubst_ _ x = x -- because it's suppose to be monomorphic

newtype PolyM testcase result schema norm m a = PolyM { unPolyM :: StateT (Polymorphic testcase result schema norm) m a }
  deriving (Functor, Applicative, Monad)

explore ::
  (Ord schema, Ord result, Ord norm, Schematic fun schema, Typed schema, Typed fun, Ord fun, Pretty schema,
  MonadTester testcase schema m, MonadPruner schema norm m) =>
  schema ->
  StateT (Polymorphic testcase result schema norm) m (Result schema)
explore t = do
  univ <- access univ
  unless (typ t `inUniverse` univ) $
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
          forM (Set.toList (Map.findWithDefault undefined ty' acc)) (\u ->
            exploreNoMGU (u `at` mgu)))

      return res { result_props = concatMap result_props (res:ress1 ++ ress2) }
    Rejected{} ->
      return res
  where
    t `at` ty =
      fromMaybe undefined (cast (unPoly ty) t)

exploreNoMGU ::
  (Ord schema, Ord result, Ord norm, Schematic fun schema, Typed schema, Typed fun, Ord fun,
  MonadTester testcase schema m, MonadPruner schema norm m) =>
  schema ->
  StateT (Polymorphic testcase result schema norm) m (Result schema)
exploreNoMGU t = do
  let ty = polyTyp (poly t)
  acc <- access accepted
  if (t `Set.member` Map.findWithDefault Set.empty ty acc) then return (Rejected []) else do
    accepted %= Map.insertWith Set.union ty (Set.singleton t)
    univ <- access univ
    schemas1 <- access schemas
    (res, schemas2) <- unPolyM (runStateT (Schemas.explore (makeSchema t)) schemas1)
    schemas ~= schemas2
    return res { result_props = map (regeneralise . fmap polySchema) (result_props res) }

addPolyType :: Monad m => Poly Type -> StateT (Polymorphic testcase result fun norm) m ()
addPolyType ty = do
  unif <- access unifiable
  univ <- access univ
  unless (ty `Map.member` unif) $ do
    let
      tys = [(ty', mgu) | ty' <- Map.keys unif, Just mgu <- [polyMgu ty ty']]
      ok ty mgu = oneTypeVar ty /= mgu && unPoly mgu `inUniverse` univ
      here = [mgu | (_, mgu) <- tys, ok mgu ty]
      there = [(ty', mgu) | (ty', mgu) <- tys, ok mgu ty']
    key ty # unifiable ~= Just (here, there)
    forM_ there $ \(ty', sub) ->
      sndLens # keyDefault ty' undefined # unifiable %= (there ++)

instance (Symbolic fun schema, Ord fun, Typed fun, Typed schema, MonadPruner schema norm m) =>
  MonadPruner (PolySchema schema) norm (PolyM testcase result schema norm m) where
  normaliser = PolyM $ do
    norm <- normaliser
    return (norm . monoSchema)
  add prop = PolyM $ do
    Universe univ <- access univ
    let insts = typeInstances (Set.toList univ) (regeneralise (fmap polySchema prop))
    mapM_ add insts

instance MonadTester testcase schema m =>
  MonadTester testcase (PolySchema schema) (PolyM testcase result schema norm m) where
  test prop = PolyM $ lift (test (fmap monoSchema prop))

-- Given a property which only contains one type variable,
-- add as much polymorphism to the property as possible.
-- e.g.    map (f :: a -> a) (xs++ys) = map f xs++map f ys
-- becomes map (f :: a -> b) (xs++ys) = map f xs++map f ys.
regeneralise :: (Symbolic fun schema, Typed schema) => Prop schema -> Prop schema
regeneralise =
  -- First replace each type variable occurrence with a fresh
  -- type variable (generalise), then unify type variables
  -- where necessary to preserve well-typedness (restrict).
  restrict . unPoly . generalise
  where
    generalise (lhs :=>: rhs) =
      polyApply (:=>:) (polyList (map genLit lhs)) (genLit rhs)
    genLit (t :=: u) = polyApply (:=:) (poly t) (poly u)

    restrict prop = typeSubst sub prop
      where
        Just sub = Twee.unifyList (Twee.buildList (map fst cs)) (Twee.buildList (map snd cs))
        cs = [(var_ty x, var_ty y) | x:xs <- vs, y <- xs] ++ concatMap litCs (lhs prop) ++ litCs (rhs prop)
        -- Two variables that were equal before generalisation must have the
        -- same type afterwards
        vs = partitionBy skel (concatMap vars (terms prop))
        skel (V ty x) = V (oneTypeVar ty) x
    litCs (t :=: u) = [(typ t, typ u)]

typeInstances :: (Symbolic fun a, Ord fun, Typed fun, Typed a) => [Type] -> Prop a -> [Prop a]
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

universe :: Typed a => [a] -> Universe
universe xs = Universe (close add (Set.fromList base))
  where
    add tys = concatMap subterms tys
    subterms (Twee.App _ ts) = Twee.unpack ts
    subterms _ = []
    base = map (oneTypeVar . typ) xs
    close f x
      | x == y = x
      | otherwise = close f y
      where
        y = x `Set.union` Set.fromList (f (Set.toList x))

inUniverse :: Type -> Universe -> Bool
ty `inUniverse` Universe x =
  oneTypeVar ty `Set.member` x
