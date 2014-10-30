{-# LANGUAGE FlexibleInstances #-}
-- https://hal.inria.fr/inria-00075875/document
module QuickSpec.Pruning.Completion where

import QuickSpec.Base hiding ((<>), nest)
import QuickSpec.Term
--import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Utils
import qualified Data.Rewriting.CriticalPair as CP
import qualified Data.Rewriting.Rule as Rule
import Data.Either
import Control.Monad
import Control.Monad.State.Strict
import Data.Maybe

type PruningTerm = Tm PruningConstant PruningVariable
type PruningConstant = String
type PruningVariable = Int
instance Sized [Char] where funSize _ = 1
v = Var
x = v 0
y = v 1
z = v 2
i = v 3
t <> u = Fun "<>" [t, u]
nest t u = Fun "nest" [t, u]

eqs = [
  (x <> (y <> z)) :==: ((x <> y) <> z),
  (x <> nest i y) :==: (x <> y)]

data Equation = PruningTerm :==: PruningTerm deriving (Eq, Ord, Show)
type Rule = Rule.Rule PruningConstant PruningVariable
type PruningCP = CP.CP PruningConstant PruningVariable PruningVariable

type T = StateT Completion
data Completion =
  Completion {
    maxSize :: Int,
    rules :: [Rule],
    cps :: [Equation] } deriving Show

initialState = Completion 20 [] []

pairs' :: Rule -> Rule -> [Equation]
pairs' e1 e2 = do
  cp <- CP.cps [e1] [e2]
  let sub = rename (either (*2) (\n->n*2+1)) . subst (CP.subst cp)
      top = sub (CP.top cp)
      left = sub (CP.left cp)
      right = sub (CP.right cp)
  guard (not (top `simplerThan` left) || Rule.rhs e1 `simplerThan` Rule.lhs e1)
  guard (not (top `simplerThan` right) || Rule.rhs e2 `simplerThan` Rule.lhs e2)
  return (if left <= right then left :==: right else right :==: left)

reduce :: [Rule] -> PruningTerm -> PruningTerm
reduce rs t =
  case reductions rs t of
    [] -> t
    (u:_) -> reduce rs u

reductions :: [Rule] -> PruningTerm -> [PruningTerm]
reductions rs t = (do
  r <- rs
  sub <- maybeToList (match (Rule.lhs r) t)
  let u = subst sub (Rule.rhs r)
  guard (u `simplerThan` t || Rule.rhs r `simplerThan` Rule.lhs r)
  return u) ++
  do
    Fun f xs <- [t]
    n <- [0..length xs-1]
    y <- reductions rs (xs !! n)
    return (Fun f (take n xs ++ [y] ++ drop (n+1) xs))  

addRule :: Monad m => Rule -> StateT Completion m ()
addRule r = do
  s <- gets maxSize
  when (size (Rule.lhs r) <= s && size (Rule.rhs r) <= s) $ do
    modify (\s -> s { rules = r:usort (map (simplifyWith r) (rules s)) })
    makeCPs
  where
    makeCPs = do
      rs <- gets rules
      let cs = concat [pairs' r r' ++ pairs' r' r | r' <- rs]
      modify (\s -> s { cps = usort (cs ++ cps s)})

simplifyWith r (Rule.Rule lhs@(Fun f xs) rhs)
  | rhs' `simplerThan` rhs = simplifyWith r (Rule.Rule lhs rhs')
  | otherwise = Rule.Rule (head (lhs' ++ [lhs])) rhs
  where
    rhs' = reduce [r] rhs
    lhs' = [ t | n <- [0..length xs-1], let y = reduce [r] (xs !! n), let t = Fun f (take n xs ++ [y] ++ drop (n+1) xs), t `simplerThan` lhs ]

addEquation :: Monad m => Equation -> StateT Completion m ()
addEquation eq@(lhs :==: rhs)
  | lhs == rhs = return ()
  | lhs `simplerThan` rhs = addRule (Rule.Rule rhs lhs)
  | rhs `simplerThan` lhs = addRule (Rule.Rule lhs rhs)
  | otherwise = addRule (Rule.Rule lhs rhs) >> addRule (Rule.Rule rhs lhs)

considerCP :: Monad m => Equation -> StateT Completion m ()
considerCP (lhs :==: rhs) = do
  rs <- gets rules
  let lhs' = reduce rs lhs
      rhs' = reduce rs rhs
  addEquation (lhs' :==: rhs')

loop :: Monad m => StateT Completion m ()
loop = do
  res <- loop1
  when res loop

loop1 :: Monad m => StateT Completion m Bool
loop1 = do
  cps_ <- gets cps
  case cps_ of
    (c:cs) -> do
      modify (\s -> s { cps = cs })
      considerCP c
      return True
    [] -> return False
