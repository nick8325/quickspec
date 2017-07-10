{-# LANGUAGE FlexibleInstances #-}
import QuickSpec.Explore.Terms
import qualified QuickSpec.Testing.QuickCheck as QC
import qualified QuickSpec.Pruning.Twee as T
import qualified QuickSpec.Pruning.EncodeTypes as ET
import qualified QuickSpec.Pruning.HigherOrder as HO
import qualified Twee.Base as B
import QuickSpec.Utils
import QuickSpec.Term
import QuickSpec.Type
import Data.List
import Data.Ord
import Test.QuickCheck
import Data.Proxy
import Data.Functor.Identity
import Data.Maybe
import Data.MemoUgly
import QuickSpec.FindInstance
import QuickSpec.Instances
import Test.QuickCheck.Gen
import Test.QuickCheck.Gen.Unsafe

data Con = Plus | Times | Zero | One
  deriving (Eq, Ord, Show)

instance Typed Con where
  typ = typ . evalConId
  typeSubst_ _ ty = ty

instance Pretty Con where
  pPrint Plus = text "+"
  pPrint Times = text "*"
  pPrint Zero = text "0"
  pPrint One = text "1"

instance PrettyTerm Con where
  termStyle Plus = infixStyle 5
  termStyle Times = infixStyle 5
  termStyle _ = curried

instance Sized Con where
  size _ = 1

instance Arity Con where
  arity = typeArity . typ . evalConId

evalCon :: Applicative f => Con -> Value f
evalCon Zero = toValue (pure (0 :: Integer))
evalCon One = toValue (pure (1 :: Integer))
evalCon Plus = toValue (pure ((+) :: Integer -> Integer -> Integer))
evalCon Times = toValue (pure ((*) :: Integer -> Integer -> Integer))

evalConId :: Con -> Value Identity
evalConId = evalCon

eval :: (Var -> Value Maybe) -> Term (HO.HigherOrder Con) -> Either Integer (Term (HO.HigherOrder Con))
eval env t =
  case fromValue (evaluateTerm (evalHO evalCon) env t) of
    Nothing -> Right t
    Just (Just n) -> Left n
  
evalHO :: Applicative g => (f -> Value g) -> HO.HigherOrder f -> Value g
evalHO fun (HO.Partial f _) = fun f
evalHO _ (HO.Apply ty) =
  fromJust $
    cast (build (app (B.fun Arrow) [ty, ty]))
      (toValue (pure (($) :: (A -> B) -> (A -> B))))

-- Term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure = (Int, Int, MeasureFuns (HO.HigherOrder Con), Int, [Var])
measure :: Term (HO.HigherOrder Con) -> Measure
measure t =
  (size t, -length (vars t),
   MeasureFuns (build (skel (singleton t))),
   -length (usort (vars t)), vars t)
  where
    skel Empty = mempty
    skel (Cons (Var (V ty x)) ts) = var (V ty 0) `mappend` skel ts
    skel (Cons (App f ts) us) =
      app f (skel ts) `mappend` skel us

newtype MeasureFuns f = MeasureFuns (Term f)
instance Ord f => Eq (MeasureFuns f) where
  t == u = compare t u == EQ
instance Ord f => Ord (MeasureFuns f) where
  compare (MeasureFuns t) (MeasureFuns u) = compareFuns t u

compareFuns :: Ord f => Term f -> Term f -> Ordering
compareFuns (Var x) (Var y) = compare x y
compareFuns Var{} App{} = LT
compareFuns App{} Var{} = GT
compareFuns (App (F f) ts) (App (F g) us) =
  compare f g `orElse`
  compare (map MeasureFuns (unpack ts)) (map MeasureFuns (unpack us))

baseTerms :: [Term (HO.HigherOrder Con)]
baseTerms =
  sortBy (comparing measure) $
    map build $
    [con (fun (HO.Partial Zero 0)),
     con (fun (HO.Partial One 0)),
     con (fun (HO.Partial Plus 0)),
     con (fun (HO.Partial Times 0))] ++
    [var (V ty n) | n <- [0..2], ty <- [tInt]]
  where
    tInt = typeRep (Proxy :: Proxy Integer)

moreTerms :: [[Term (HO.HigherOrder Con)]] -> [Term (HO.HigherOrder Con)]
moreTerms tss =
  sortBy' measure $
    [ v
    | i <- [0..n-1],
      t <- tss !! i,
      u <- tss !! (n-i),
      Just v <- [tryApply t u] ]
  where
    n = length tss

arbitraryVal :: Instances -> Gen (Var -> Value Maybe)
arbitraryVal insts =
  MkGen $ \g n -> memo $ \(V ty x) ->
    case typ ty of
      Nothing ->
        fromJust $ cast ty (toValue (Nothing :: Maybe A))
      Just gen ->
        forValue gen $ \gen ->
          Just (unGen (coarbitrary x gen) g n)
  where
    typ :: Type -> Maybe (Value Gen)
    typ = memo $ \ty ->
      case findInstance insts ty of
        [] -> Nothing
        (gen:_) ->
          Just (mapValue (coarbitrary ty) gen)

main = do
  tester <-
    generate $ QC.quickCheckTester
      QC.Config { QC.cfg_num_tests = 1000, QC.cfg_max_test_size = 100 }
      (arbitraryVal baseInstances)
      eval

  let
    size = 7
    pruner =
      HO.encodeHigherOrder $
      ET.encodeMonoTypes $
      T.tweePruner T.Config { T.cfg_max_term_size = size, T.cfg_max_cp_depth = 2 }
    state0 = initialState (flip eval) tester pruner

  loop state0 size [[]] [] baseTerms
  where
    loop state 1 _ _ [] = return ()
    loop state n tss ts [] =
      loop state (n-1) uss [] (moreTerms uss)
      where
        uss = tss ++ [ts]
    loop state n tss us (t:ts) = do
      let (state', mprop) = explore t state
      case mprop of
        Redundant ->
          loop state' n tss us ts
        Unique ->
          loop state' n tss (t:us) ts
        Discovered prop -> do
          prettyPrint prop
          loop state' n tss us ts
