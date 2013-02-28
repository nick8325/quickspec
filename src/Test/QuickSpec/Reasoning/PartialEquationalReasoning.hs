-- | Equational reasoning that deals with partial functions.
--   Only used in HipSpec at the moment.

{-# LANGUAGE CPP #-}
module Test.QuickSpec.Reasoning.PartialEquationalReasoning where

#include "../errors.h"
import Test.QuickSpec.Equation
import Test.QuickSpec.Term hiding (Variable, vars)
import qualified Test.QuickSpec.Term as Term
import Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as EQ
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning(EQ, evalEQ, runEQ)
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad.State
import qualified Control.Monad.State as S
import Data.List
import Data.Ord
import Test.QuickSpec.Utils
import Test.QuickSpec.Signature hiding (vars)
import Data.Monoid

data PEquation = Precondition :\/: Equation
type Precondition = [Symbol]
data Totality = Partial | Total [Int] | Variable deriving (Eq, Ord, Show)

instance Eq PEquation where
  e1 == e2 = e1 `compare` e2 == EQ

instance Ord PEquation where
  compare = comparing stamp
    where stamp (pre :\/: eq) = (eq, length pre, usort pre)

instance Show PEquation where
  show = showPEquation mempty

showPEquation :: Sig -> PEquation -> String
showPEquation sig (pre :\/: t :=: u) =
  showPre ((Term.vars t ++ Term.vars u) \\ pre) ++
  show (f t) ++ " == " ++ show (f u)
  where f = disambiguate sig (Term.vars t ++ Term.vars u ++ pre)
        showPre [] = ""
        showPre xs = intercalate " && " [ "total(" ++ show (f (Var x)) ++ ")" | x <- xs ] ++ " => "

infix 5 :\/:

data Context = Context {
  total :: EQ.Context,
  partial :: IntMap EQ.Context,
  vars :: IntMap Symbol
  }

type PEQ = State Context

initial :: Int -> [(Symbol, Totality)] -> [Tagged Term] -> Context
initial d syms univ
  | ok syms = Context total partial vars
  | otherwise = __
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
           (ERROR "type not found")
           (index x) totality of
        Partial -> False
        Total pre -> and [ isTotal ctx [] arg || i `elem` pre | (i, arg) <- zip [0..] args ]
        Variable -> __
    vars = IntMap.fromList [(index s, s) | (s, Variable) <- syms]

runPEQ :: Context -> PEQ a -> (a, Context)
runPEQ = flip runState

evalPEQ :: Context -> PEQ a -> a
evalPEQ ctx x = fst (runPEQ ctx x)

execPEQ :: Context -> PEQ a -> Context
execPEQ ctx x = snd (runPEQ ctx x)

liftEQ :: [Int] -> (Maybe Int -> EQ a) -> PEQ [a]
liftEQ pre x = do
  Context total partial vars <- S.get
  let (totalRes, total') = runEQ total (x Nothing)
      (partialRes, partial') = IntMap.mapAccumWithKey f [] partial
      f rs i ctx
        | i `elem` pre = runEQ ctx (fmap (:rs) (x (Just i)))
        | otherwise = (rs, ctx)
  S.put (Context total' partial' vars)
  return (totalRes:partialRes)

equal :: PEquation -> PEQ Bool
equal (pre :\/: t :=: u) = liftM2 (==) (rep pre t) (rep pre u)

irrelevant :: Equation -> PEQ Precondition
irrelevant (t :=: u) = do
  vs <- gets (IntMap.elems . vars)
  return (vs \\ (Term.vars t `intersect` Term.vars u))

unify :: PEquation -> PEQ Bool
unify (pre :\/: eq) = do
  irr <- irrelevant eq
  fmap and . liftEQ (map index (pre ++ irr)) $ \n ->
    case n of
      Just i | i `notElem` map index pre -> return True
      _ -> EQ.unify eq

precondition :: Equation -> PEQ Precondition
precondition eq = do
  Context _ partial vars <- S.get
  fmap concat . liftEQ (IntMap.keys partial) $ \n ->
    case n of
      Nothing -> return []
      Just i -> do
        r <- EQ.equal eq
        if r then
           return [IntMap.findWithDefault (ERROR "precondition: var not found") i vars]
          else return []

get :: PEQ Context
get = S.get

put :: Context -> PEQ ()
put = S.put

rep :: Precondition -> Term -> PEQ [Int]
rep pre t = liftEQ (map index pre) (const (EQ.rep t))