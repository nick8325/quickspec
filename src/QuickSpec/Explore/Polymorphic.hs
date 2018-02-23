-- Theory exploration which handles polymorphism.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts, GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses, BangPatterns, UndecidableInstances, RankNTypes, GADTs, RecordWildCards #-}
module QuickSpec.Explore.Polymorphic(module QuickSpec.Explore.Polymorphic, Result(..)) where

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
import Data.Maybe
import qualified Data.DList as DList

data Polymorphic testcase result fun norm =
  Polymorphic {
    pm_schemas :: Schemas testcase result (PolyFun fun) norm,
    pm_unifiable :: Map (Poly Type) ([Poly Type], [(Poly Type, Poly Type)]),
    pm_accepted :: Map (Poly Type) (Set (Term fun)),
    pm_universe :: Universe }

data PolyFun fun =
  PolyFun { fun_original :: fun, fun_specialised :: fun }
  deriving (Eq, Ord)

instance Pretty fun => Pretty (PolyFun fun) where
  pPrint = pPrint . fun_specialised

instance PrettyTerm fun => PrettyTerm (PolyFun fun) where
  termStyle = termStyle . fun_specialised

-- univ_inner: the type universe, with all type variables unified
-- univ_root: the set of types allowed for partially applied functions, only at
-- the root of a term
data Universe = Universe { univ_inner :: Set Type, univ_root :: Set Type }

makeLensAs ''Polymorphic
  [("pm_schemas", "schemas"),
   ("pm_unifiable", "unifiable"),
   ("pm_accepted", "accepted"),
   ("pm_universe", "univ")]

initialState ::
  Universe ->
  (Term fun -> Bool) ->
  (Term fun -> testcase -> result) ->
  Polymorphic testcase result fun norm
initialState univ inst eval =
  Polymorphic {
    pm_schemas = Schemas.initialState (inst . fmap fun_specialised) (eval . fmap fun_specialised),
    pm_unifiable = Map.empty,
    pm_accepted = Map.empty,
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
    let ty = polyTyp (poly t)
    addPolyType ty

    unif <- access unifiable
    let (here, there) = Map.findWithDefault undefined ty unif
    acc <- access accepted
    ress1 <-
      concat <$>
      forM there (\(ty', mgu) ->
        forM (Set.toList (Map.findWithDefault undefined ty' acc)) (\u ->
          exploreNoMGU (u `at` mgu)))
    res <- exploreNoMGU t
    ress2 <-
      forM here (\mgu ->
        exploreNoMGU (t `at` mgu))
    return res { result_props = concatMap result_props (ress1 ++ [res] ++ ress2) }
    where
      t `at` ty =
        fromMaybe undefined (cast (unPoly ty) t)

exploreNoMGU ::
  (PrettyTerm fun, Ord result, Ord norm, Typed fun, Ord fun, Apply (Term fun),
  MonadTester testcase (Term fun) m, MonadPruner (Term fun) norm m) =>
  Term fun ->
  StateT (Polymorphic testcase result fun norm) m (Result fun)
exploreNoMGU t = do
  univ <- access univ
  let ty = polyTyp (poly t)
  acc <- access accepted
  if (t `Set.member` Map.findWithDefault Set.empty ty acc ||
      not (t `inUniverse` univ)) then return (Rejected []) else do
    accepted %= Map.insertWith Set.union ty (Set.singleton t)
    schemas1 <- access schemas
    (res, schemas2) <- unPolyM (runStateT (Schemas.explore (polyTerm t)) schemas1)
    schemas ~= schemas2
    return (mapProps (regeneralise . mapFun fun_original) res)
  where
    mapProps f (Accepted props) = Accepted (map f props)
    mapProps f (Rejected props) = Rejected (map f props)

addPolyType :: Monad m => Poly Type -> StateT (Polymorphic testcase result fun norm) m ()
addPolyType ty = do
  unif <- access unifiable
  univ <- access univ
  unless (ty `Map.member` unif) $ do
    let
      tys = [(ty', mgu) | ty' <- Map.keys unif, Just mgu <- [polyMgu ty ty']]
      ok ty mgu = oneTypeVar ty /= mgu && oneTypeVar (unPoly mgu) `Set.member` univ_root univ
      here = [mgu | (_, mgu) <- tys, ok mgu ty]
      there = [(ty', mgu) | (ty', mgu) <- tys, ok mgu ty']
    key ty # unifiable ~= Just (here, there)
    forM_ there $ \(ty', _) ->
      sndLens # keyDefault ty' undefined # unifiable %= (there ++)

instance (PrettyTerm fun, Ord fun, Typed fun, Apply (Term fun), MonadPruner (Term fun) norm m) =>
  MonadPruner (Term (PolyFun fun)) norm (PolyM testcase result fun norm m) where
  normaliser = PolyM $ do
    norm <- normaliser
    return (norm . fmap fun_specialised)
  add prop = PolyM $ do
    univ <- access univ
    let insts = typeInstances univ (regeneralise (mapFun fun_original prop))
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

typeInstances :: (Pretty a, PrettyTerm fun, Symbolic fun a, Ord fun, Typed fun, Typed a) => Universe -> a -> [a]
typeInstances Universe{..} prop =
  [ typeSubst (\x -> Map.findWithDefault (error ("not found: " ++ prettyShow x)) x sub) prop
  | sub <- cs ]
  where
    cs =
      foldr intersection [Map.empty]
        (map (constrain (Set.toList univ_inner))
          (usort (DList.toList (termsDL prop) >>= properSubterms)) ++
         map (constrain (Set.toList univ_root))
          (usort (DList.toList (termsDL prop))))

    constrain tys t =
      usort [ Map.fromList (Twee.substToList sub) | u <- tys, Just sub <- [Twee.match (typ t) u] ]

intersection :: [Map Twee.Var Type] -> [Map Twee.Var Type] -> [Map Twee.Var Type]
ms1 `intersection` ms2 = usort [ Map.union m1 m2 | m1 <- ms1, m2 <- ms2, ok m1 m2 ]
  where
    ok m1 m2 = and [ Map.lookup x m1 == Map.lookup x m2 | x <- Map.keys (Map.intersection m1 m2) ]

universe :: Typed a => [a] -> Universe
universe xs = Universe (Set.fromList base) (Set.fromList (withFunctions base))
  where
    -- The universe contains the type variable "a", the argument and
    -- result type of every function (with all type variables unified), and all
    -- subterms of these types
    base = usort $ typeVar:concatMap (oneTypeVar . typs . typ) xs
    typs ty = (typeRes ty:typeArgs ty) >>= Twee.subterms

    -- We then add partial applications, according to the rule:
    -- if f : A1 -> ... -> An -> B is a function in the signature,
    -- and s(A1)...s(An), s(B) are in the universe where s is a substitution,
    -- then s(A1 -> ... -> An -> B) is in the universe, together with all subterms
    withFunctions tys =
      tys ++
      concat [func Twee.emptySubst (typ f) tys >>= Twee.subterms | f <- xs]

    func sub ty tys =
      filter (`elem` tys) [oneTypeVar (typeSubst sub ty)] ++
      [ arrowType [t'] u'
      | Just (t, u) <- [unpackArrow ty],
        t' <- tys,
        Just sub <- [Twee.matchIn sub t t'],
        u' <- func sub u tys ]

inUniverse :: Typed fun => Term fun -> Universe -> Bool
t `inUniverse` Universe{..} =
  and [oneTypeVar (typ u) `Set.member` univ_inner | u <- subterms t]

usefulForUniverse :: Typed fun => Term fun -> Universe -> Bool
t `usefulForUniverse` Universe{..} =
  oneTypeVar (typ t) `Set.member` univ_root &&
  and [oneTypeVar (typ u) `Set.member` univ_inner | u <- properSubterms t]
