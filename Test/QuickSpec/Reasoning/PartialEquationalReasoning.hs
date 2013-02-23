-- | Equational reasoning that deals with partial functions.
--   Only used in HipSpec at the moment.

module Test.QuickSpec.Reasoning.PartialEquationalReasoning where

import Test.QuickSpec.Equation
import Test.QuickSpec.Term hiding (Variable)
import Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as EQ
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning(EQ, evalEQ, runEQ)
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad.State
import qualified Control.Monad.State as S

data PEquation = Precondition :\/: Equation
type Precondition = [Int]
data Totality = Partial | Total Precondition | Variable

infix 5 :\/:

data Context = Context {
  total :: EQ.Context,
  partial :: IntMap EQ.Context
  }

type PEQ = State Context

initial :: Int -> [(Symbol, Totality)] -> [Tagged Term] -> Context
initial d syms univ
  | ok syms = Context total partial
  | otherwise = error "PartialEquationalReasoning.initial: bad input"
  where
    ok syms = and (zipWith (==) [0..] (map (index . fst) syms))
    total = EQ.initial d (map fst syms) (filter (isTotal Nothing [] . erase) univ)
    partial = IntMap.fromList [
      (i, EQ.initial d (map fst syms) (filter (isTotal (Just i) [] . erase) univ))
      | (i, (sym, Variable)) <- zip [0..] syms
      ]
    totality = IntMap.fromList [(index sym, tot) | (sym, tot) <- syms]
    isTotal ctx args (Var x) = ctx /= Just (index x) && all (isTotal ctx []) args
    isTotal ctx args (App f x) = isTotal ctx (x:args) f
    isTotal ctx args (Const x) =
      case IntMap.findWithDefault
           (error "PartialEquationalReasoning.initial: type not found")
           (index x) totality of
        Partial -> False
        Total pre -> and [ isTotal ctx [] arg || i `elem` pre | (i, arg) <- zip [0..] args ]
        Variable -> error "PartialEquationalReasoning.initial: inappropriate term"
      
runPEQ :: Context -> PEQ a -> (a, Context)
runPEQ = flip runState

evalPEQ :: Context -> PEQ a -> a
evalPEQ ctx x = fst (runPEQ ctx x)

execPEQ :: Context -> PEQ a -> Context
execPEQ ctx x = snd (runPEQ ctx x)

liftEQ :: Precondition -> (Maybe Int -> EQ a) -> PEQ [a]
liftEQ pre x = do
  Context total partial <- S.get
  let (totalRes, total') = runEQ total (x Nothing)
      (partialRes, partial') = IntMap.mapAccumWithKey f [] partial
      f rs i ctx
        | i `elem` pre = runEQ ctx (fmap (:rs) (x (Just i)))
        | otherwise = (rs, ctx)
  S.put (Context total' partial')
  return (totalRes:partialRes)

equal :: PEquation -> PEQ Bool
equal (pre :\/: t :=: u) = liftM2 (==) (rep pre t) (rep pre u) 

unify :: PEquation -> PEQ Bool
unify (pre :\/: eq) = do
  fmap and . liftEQ pre $ \n -> 
    case n of
      Just i | i `notElem` pre -> return True
      _ -> EQ.unify eq

get :: PEQ Context
get = S.get

put :: Context -> PEQ ()
put = S.put

rep :: Precondition -> Term -> PEQ [Int]
rep pre t = liftEQ pre (const (EQ.rep t))