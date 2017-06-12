{-# LANGUAGE FlexibleInstances #-}
import QuickSpec.Explore.Terms
import qualified QuickSpec.Testing.QuickCheck as QC
import qualified QuickSpec.Pruning.Twee as T
import qualified QuickSpec.Pruning.EncodeTypes as ET
import qualified Twee.Base as B
import qualified Twee.KBO as KBO
import QuickSpec.Utils
import QuickSpec.Term
import QuickSpec.Type
import Data.List
import Data.Ord
import Test.QuickCheck
import Data.Proxy

data Con = Plus | Times | Zero | One
  deriving (Eq, Ord, Show)

instance Typed Con where
  typ Plus = typeOf ((+) :: Integer -> Integer -> Integer)
  typ Times = typeOf ((*) :: Integer -> Integer -> Integer)
  typ Zero = typeOf (0 :: Integer)
  typ One = typeOf (1 :: Integer)
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
  arity Plus = 2
  arity Times = 2
  arity Zero = 0
  arity One = 0

instance Ordered (Extended (ET.Tagged Con)) where
  lessEq t u = KBO.lessEq t u
  lessIn model t  u = KBO.lessIn model t u

eval :: (Int -> Integer) -> Term Con -> Integer
eval env (Var (V _ x)) = env x
eval _ (App (F Zero) Empty) = 0
eval _ (App (F One) Empty) = 1
eval env (App (F Plus) (Cons t (Cons u Empty))) =
  eval env t + eval env u
eval env (App (F Times) (Cons t (Cons u Empty))) =
  eval env t * eval env u

-- Term ordering - size, skeleton, generality.
-- Satisfies the property:
-- if measure (schema t) < measure (schema u) then t < u.
type Measure = (Int, Int, MeasureFuns Con, Int, [Var])
measure :: Term Con -> Measure
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

allTerms :: [Term Con]
allTerms = sortBy (comparing measure) $ concat (take 8 tss)
  where
    tss = map sized [0..]
    sized 0 = []
    sized 1 =
      map build $
      [con (fun Zero), con (fun One)] ++
      [var (V ty n) | n <- [0..2], ty <- [tInt]]
    sized n =
      [ build (app (fun f) [t, u])
      | f <- [Plus, Times],
        i <- [0..n-1],
        t <- tss !! i,
        u <- tss !! (n-1-i) ]
    tInt = typeRep (Proxy :: Proxy Integer)

main = do
  tester <-
    generate $ QC.quickCheckTester
      QC.Config { QC.cfg_num_tests = 1000, QC.cfg_max_test_size = 100 }
      arbitrary
      eval

  let
    pruner =
      ET.encodeMonoTypes $
      T.tweePruner T.Config { T.cfg_max_term_size = 7, T.cfg_max_cp_depth = 2 }
    state0 = initialState (flip eval) tester pruner

  loop state0 allTerms
  where
    loop state [] = return ()
    loop state (t:ts) = do
      let (state', mprop) = explore t state
      case mprop of
        Nothing -> return ()
        Just prop -> prettyPrint prop
      loop state' ts
