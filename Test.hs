{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses #-}
import QuickSpec.Explore.Terms
import qualified QuickSpec.Testing.QuickCheck as QC
import qualified QuickSpec.Pruning.Twee as T
import qualified QuickSpec.Pruning.EncodeTypes as ET
import QuickSpec.Explore.PartialApplication
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
import QuickSpec.Haskell
import Test.QuickCheck.Gen
import Test.QuickCheck.Gen.Unsafe
import qualified Data.Typeable as Ty
import Data.Constraint

type Con = PartiallyApplied Constant

constants :: [Constant]
constants = [
  constant "+" ((+) :: Int -> Int -> Int),
  constant "*" ((*) :: Int -> Int -> Int),
  constant "0" (0 :: Int),
  constant "1" (1 :: Int)]

baseTerms :: [Term Con]
baseTerms =
  sortBy (comparing measure) $
    map build $
    [con (fun (Partial f 0)) | f <- constants] ++
    [var (V ty n) | n <- [0..2], ty <- [tInt, tList]]
  where
    tInt = typeRep (Proxy :: Proxy Int)
    tList = typeRep (Proxy :: Proxy [Char])

moreTerms :: [[Term Con]] -> [Term Con]
moreTerms tss =
  sortBy' measure $
    [ v
    | i <- [0..n-1],
      t <- tss !! i,
      u <- tss !! (n-i),
      Just v <- [tryApply t u] ]
  where
    n = length tss

main = do
  tester <-
    generate $ QC.quickCheckTester
      QC.Config { QC.cfg_num_tests = 1000, QC.cfg_max_test_size = 100 }
      (arbitraryVal baseInstances)
      (evalHaskell baseInstances)

  let
    size = 7
    pruner =
      encodePartialApplications $
      ET.encodeMonoTypes $
      T.tweePruner T.Config { T.cfg_max_term_size = size, T.cfg_max_cp_depth = 2 }
    state0 = initialState (flip (evalHaskell baseInstances)) tester pruner

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
