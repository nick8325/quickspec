{-# LANGUAGE FlexibleInstances, GADTs #-}
import QuickSpec.Explore.Terms
import qualified QuickSpec.Testing.QuickCheck as QC
import qualified QuickSpec.Pruning.Twee as T
import qualified QuickSpec.Pruning.EncodeTypes as ET
import qualified QuickSpec.Explore.PartialApplication as P
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

data Con = Plus | Times | Zero | One | Length | Append | Nil | Rev | Id
  deriving (Eq, Ord, Show, Bounded, Enum)

instance Typed Con where
  typ = typ . (evalCon :: Con -> Value Identity)
  typeSubst_ _ ty = ty

instance Pretty Con where
  pPrint Plus = text "+"
  pPrint Times = text "*"
  pPrint Zero = text "0"
  pPrint One = text "1"
  pPrint Length = text "length"
  pPrint Append = text "++"
  pPrint Nil = text "[]"
  pPrint Rev = text "reverse"
  pPrint Id = text "id"

instance PrettyTerm Con where
  termStyle Plus = infixStyle 5
  termStyle Times = infixStyle 5
  termStyle Append = infixStyle 5
  termStyle _ = curried

instance Sized Con where
  size _ = 1

instance Arity Con where
  arity = typeArity . typ

evalCon :: Applicative f => Con -> Value f
evalCon Zero = toValue (pure (0 :: Integer))
evalCon One = toValue (pure (1 :: Integer))
evalCon Plus = toValue (pure ((+) :: Integer -> Integer -> Integer))
evalCon Times = toValue (pure ((*) :: Integer -> Integer -> Integer))
evalCon Length = toValue (pure (fromIntegral . length :: [Char] -> Integer))
evalCon Append = toValue (pure ((++) :: [Char] -> [Char] -> [Char]))
evalCon Nil = toValue (pure ([] :: [Char]))
evalCon Rev = toValue (pure (reverse :: [Char] -> [Char]))
evalCon Id = toValue (pure (id :: [Char] -> [Char]))

baseTerms :: [Term (P.PartiallyApplied Con)]
baseTerms =
  sortBy (comparing measure) $
    map build $
    [con (fun (P.Partial f 0)) | f <- [minBound..maxBound]] ++
    [var (V ty n) | n <- [0..2], ty <- [tInt, tList]]
  where
    tInt = typeRep (Proxy :: Proxy Integer)
    tList = typeRep (Proxy :: Proxy [Char])

moreTerms :: [[Term (P.PartiallyApplied Con)]] -> [Term (P.PartiallyApplied Con)]
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
      (eval baseInstances (P.evalPartiallyApplied evalCon))

  let
    size = 7
    pruner =
      P.encodePartialApplications $
      ET.encodeMonoTypes $
      T.tweePruner T.Config { T.cfg_max_term_size = size, T.cfg_max_cp_depth = 2 }
    state0 = initialState (flip (eval baseInstances (P.evalPartiallyApplied evalCon))) tester pruner

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
