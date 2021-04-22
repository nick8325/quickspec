-- A simple example testing arithmetic functions.
{-# LANGUAGE TupleSections, TypeSynonymInstances, FlexibleInstances #-}
import QuickSpec hiding (A)
import QuickSpec.Internal hiding (A)
import qualified QuickSpec.Internal.Haskell as Haskell
import Test.QuickCheck
import Twee.Pretty
import Control.Monad
import Data.Matrix
import Data.Ord
import Data.Either
import Data.Vector(Vector)
import Data.Complex
import Numeric.Natural
import Test.QuickCheck.Instances

dim = 5

type A = Rational
type T = Matrix A

instance Ord a => Ord (Matrix a) where
  compare = comparing toLists

instance (RealFrac a, Ord a) => Ord (Complex a) where
  compare = comparing (\(x :+ y) -> (truncate (x*1000), truncate (y*1000)))

--instance Ord Cyclotomic where
--  compare = comparing show
--
--instance Arbitrary Cyclotomic where
--  arbitrary = sized arb
--    where
--      arb n =
--        frequency $
--          [(5, fromInteger  <$> arbitrary),
--           (5, fromRational <$> arbRat),
--           (5, gaussianRat <$> arbRat <*> arbRat),
--           (5, polarRat <$> arbRat <*> arbRat),
--           (5, e <$> fmap (succ . abs) arbitrary),
--           (3, sqrtInteger <$> arbitrary),
--           (3, sqrtRat <$> arbRat),
--           (2, sinRev <$> arbRat),
--           (2, cosRev <$> arbRat),
--           (2, return i)] ++
--          concat
--            [ [(5, conj <$> arb (n-1)),
--               (3, real <$> arb (n-1)),
--               (3, imag <$> arb (n-1))]
--            | n > 0 ] ++
--          concat
--            [ let arb2 = arb (n `div` 2) in
--              [(n*5, (+) <$> arb2 <*> arb2),
--               (n*5, (*) <$> arb2 <*> arb2)]
--            | n > 0 ]
--      arbRat = sized $ \n -> do
--        x <- choose (-(n `min` 3), n `min` 3)
--        d <- fmap (succ . abs) (choose (0, n `min` 5))
--        n <- choose (0, d-1)
--        return (fromIntegral x + fromIntegral n / fromIntegral d)

instance Arbitrary T where
  arbitrary =
    makeHermitian <$> frequency [
--(1, return $ zero dim dim),
--      (1, return $ identity dim),
--      (1, return $ negate $ identity dim),
--      (1, genDiagonal),
      (5, fromList dim dim <$> infiniteListOf genA)]

genA :: Gen A
genA = fromInteger <$> arbitrary

genDiagonal :: Gen T
genDiagonal = diagonalList dim 0 <$> infiniteListOf genA

isDiagonal :: T -> Bool
isDiagonal m = m == diagonal 0 (getDiag m)

makeUpperTriangular :: T -> T
makeUpperTriangular = mapPos (\(i, j) x -> if i > j then 0 else x)

isUpperTriangular :: T -> Bool
isUpperTriangular m = makeUpperTriangular m == m

genUpperTriangular :: Gen T
genUpperTriangular = makeUpperTriangular <$> arbitrary

makeLowerTriangular :: T -> T
makeLowerTriangular = mapPos (\(i, j) x -> if i > j then 0 else x)

isLowerTriangular :: T -> Bool
isLowerTriangular m = makeLowerTriangular m == m

genLowerTriangular :: Gen (T)
genLowerTriangular = makeLowerTriangular <$> arbitrary

makeHermitian :: T -> T
makeHermitian m = m + {-fmap conjugate-} (transpose m)

isHermitian :: T -> Bool
isHermitian m = m == {-fmap conjugate-} (transpose m)

genHermitian :: Gen T
genHermitian = makeHermitian <$> arbitrary

instance Floating Rational where
  sqrt = error "sqrt"
instance RealFloat Rational

newtype RowV = RowV {unRowV :: T} deriving (Eq, Ord)
newtype ColV = ColV {unColV :: T} deriving (Eq, Ord)

instance Arbitrary RowV where
  arbitrary = RowV <$> oneof [return $ zero 1 dim, fromList 1 dim <$> infiniteList]
instance Arbitrary ColV where
  arbitrary = ColV <$> transpose <$> unRowV <$> arbitrary

times :: T -> T -> T
times x y = scaleMatrix (1/2) (x*y+y*x)

pow :: Natural -> T -> T
pow 1 t = t
pow n t | n > 0 = times t (pow (n-1) t)

main = quickSpec [
  series [
    background $
    [withMaxTermSize 7,
     -- Good pruning settings for Hard Maths (TM)
     --withPruningTermSize 9,
     arith (Proxy :: Proxy A),
     arith (Proxy :: Proxy Natural) `without` ["0"],
     con "*" ((*) :: Natural -> Natural -> Natural),
     monoType (Proxy :: Proxy T),
     con "0" (zero dim dim :: T),
     con "I" (identity dim :: T),
     con "+" ((+) :: T -> T -> T),
     vars ["A", "B", "C"] (Proxy :: Proxy T),
     vars ["n", "m", "l"] (Proxy :: Proxy Natural),
     instFun (arbitrary `suchThat` (\n -> n > 0 && n < 4) :: Gen Natural)],
     --con "*" ((*) :: T -> T -> T),
     --con "-" (negate :: T -> T)],
    --[(con "&&" (&&))],
    --[predicateGen "hermitian" isHermitian (\() -> liftM2 (,) genHermitian (return ()))],
    con "∘" times,
    con "^" (flip pow)]]
{-    [--con "perm" (permMatrix dim :: Int -> Int -> T),
     con "transpose" (transpose :: T -> T),
     --con "inverse" (either (const Nothing) Just . (inverse :: T -> Either String T)),
     con "trace" (trace :: T -> A),
     con "diagProd" (diagProd :: T -> A),
     con "det" (detLU :: T -> A)],
     {-predicateGen "isDiagonal" isDiagonal (\() -> liftM2 (,) genDiagonal (return ())),
     predicateGen "isUpperTriangular" isUpperTriangular (\() -> liftM2 (,) genUpperTriangular (return ())),
     predicateGen "isLowerTriangular" isLowerTriangular (\() -> liftM2 (,) genLowerTriangular (return ()))],-}
    [monoType (Proxy :: Proxy RowV),
     con "0R" (RowV (zero 1 dim)),
     con "+R" (\(RowV x) (RowV y) -> RowV (x+y)),
     con "*R" (\(RowV x) y -> RowV (x*y)),
     con "-R" (\(RowV x) -> RowV (negate x))],
    [con "transposeR" (\(RowV x) -> ColV (transpose x)),
     con "detR" (detLU . unRowV)],
    [monoType (Proxy :: Proxy ColV),
     con "0C" (ColV (zero dim 1)),
     con "+C" (\(ColV x) (ColV y) -> ColV (x+y)),
     con "*C" (\(ColV x) y -> ColV (x*y)),
     con "-C" (\(ColV x) -> ColV (negate x))],
    [con "transposeC" (\(ColV x) -> RowV (transpose x)),
     con "detC" (detLU . unColV)]]]-}
