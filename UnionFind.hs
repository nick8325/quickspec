module UnionFind(UF, Replacement((:>)), newSym, (=:=), rep, evalUF, execUF, runUF, S, isRep, initial) where

import Prelude hiding (min)
import Control.Monad.State.Strict
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap

data S = S {
      links :: IntMap Int,
      sym :: Int
    }

type UF = State S
data Replacement = Int :> Int

runUF :: S -> UF a -> (a, S)
runUF s m = runState m s

evalUF :: S -> UF a -> a
evalUF s m = fst (runUF s m)

execUF :: S -> UF a -> S
execUF s m = snd (runUF s m)

initial :: Int -> S
initial n = S IntMap.empty n

modifyLinks f = modify (\s -> s { links = f (links s) })
modifySym f = modify (\s -> s { sym = f (sym s) })
putLinks l = modifyLinks (const l)

newSym :: UF Int
newSym = do
  s <- get
  modifySym (+1)
  return (sym s)

(=:=) :: Int -> Int -> UF (Maybe Replacement)
s =:= t | s == t = return Nothing
s =:= t = do
  rs <- rep s
  rt <- rep t
  if (rs /= rt) then do
    modifyLinks (IntMap.insert rs rt)
    return (Just (rs :> rt))
   else return Nothing

rep :: Int -> UF Int
rep t = do
  m <- fmap links get
  case IntMap.lookup t m of
    Nothing -> return t
    Just t' -> do
      r <- rep t'
      when (t' /= r) $ modifyLinks (IntMap.insert t r)
      return r

isRep :: Int -> UF Bool
isRep t = do
  t' <- rep t
  return (t == t')
