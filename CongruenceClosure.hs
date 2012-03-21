-- Based on the paper "Proof-producing Congruence Closure".

module CongruenceClosure(CC, newSym, (=:=), (=?=), rep, evalCC, execCC, runCC, ($$), S, funUse, argUse, lookup, initial) where

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import UnionFind(UF, Replacement((:>)))
import qualified UnionFind as UF
import Data.Maybe
import Data.List(foldl')
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Monadic
import Text.Printf

lookup2 :: Int -> Int -> IntMap (IntMap a) -> Maybe a
lookup2 k1 k2 m = IntMap.lookup k2 (IntMap.findWithDefault IntMap.empty k1 m)

insert2 :: Int -> Int -> a -> IntMap (IntMap a) -> IntMap (IntMap a)
insert2 k1 k2 v m = IntMap.insertWith IntMap.union k1 (IntMap.singleton k2 v) m

delete2 :: Int -> Int -> IntMap (IntMap a) -> IntMap (IntMap a)
delete2 k1 k2 m = IntMap.adjust (IntMap.delete k2) k1 m

data FlatEqn = (Int, Int) := Int deriving (Eq, Ord)

data S = S {
      -- in all these maps, the keys are representatives, the values may not be
      funUse :: !(IntMap [(Int, Int)]),
      argUse :: !(IntMap [(Int, Int)]),
      lookup :: IntMap (IntMap Int),
      uf :: UF.S
    }

type CC = State S

liftUF :: UF a -> CC a
liftUF m = do
  s <- get
  let (x, uf') = UF.runUF (uf s) m
  put s { uf = uf' }
  return x

invariant :: String -> CC ()
invariant _ = return ()
-- invariant str = do
--   S funUse argUse lookup <- get
--   -- keys of all maps are representatives
--   let check phase x = do
--        b <- liftUF (UF.isRep x)
--        if b then return () else error (printf "%s, %s appears as a key in %s but is not a rep in:\nfunUse=%s\nargUse=%s\nlookup=%s" str (show x) phase (show funUse) (show argUse) (show lookup))
--   mapM_ (check "funUse") (IntMap.keys funUse)
--   mapM_ (check "argUse") (IntMap.keys argUse)
--   mapM_ (check "lookup") (IntMap.keys lookup)
--   mapM_ (mapM_ (check "inner lookup") . IntMap.keys) (IntMap.elems lookup)

modifyFunUse f = modify (\s -> s { funUse = f (funUse s) })
modifyArgUse f = modify (\s -> s { argUse = f (argUse s) })
addFunUses xs s = modifyFunUse (IntMap.insertWith (++) s xs)
addArgUses xs s = modifyArgUse (IntMap.insertWith (++) s xs)
modifyLookup f = modify (\s -> s { lookup = f (lookup s) })
putLookup l = modifyLookup (const l)

newSym :: CC Int
newSym = liftUF UF.newSym

($$) :: Int -> Int -> CC Int
f $$ x = do
  invariant (printf "before %s$$%s" (show f) (show x))
  m <- gets lookup
  f' <- rep f
  x' <- rep x
  invariant (printf "at %s$$%s:1" (show f) (show x))
  case lookup2 x' f' m of
    Nothing -> do
      c <- newSym
      invariant (printf "at %s$$%s:2" (show f) (show x))
      putLookup (insert2 x' f' c m)
      addFunUses [(x', c)] f'
      addArgUses [(f', c)] x'
      invariant (printf "after %s$$%s" (show f) (show x))
      return c
    Just k -> return k

(=:=) :: Int -> Int -> CC Bool
a =:= b = propagate (a, b)

(=?=) :: Int -> Int -> CC Bool
t =?= u = liftM2 (==) (rep t) (rep u)

propagate (a, b) = do
  (unified, pending) <- propagate1 (a, b)
  mapM_ propagate pending
  return unified

propagate1 (a, b) = do
  invariant (printf "before propagate (%s, %s)" (show a) (show b))
  res <- liftUF (a UF.=:= b)
  case res of
    Nothing -> return (False, [])
    Just (r :> r') -> do
      funUses <- gets (IntMap.lookup r . funUse)
      argUses <- gets (IntMap.lookup r . argUse)
      case (funUses, argUses) of
        (Nothing, Nothing) -> return (True, [])
        _ -> fmap (\x -> (True, x)) (updateUses r r' (fromMaybe [] funUses) (fromMaybe [] argUses))

updateUses r r' funUses argUses = do
  modifyFunUse (IntMap.delete r)
  modifyArgUse (IntMap.delete r)
  modifyLookup (IntMap.delete r)
  forM_ funUses $ \(x, _) -> do
    x' <- rep x
    modifyLookup (delete2 x' r)
  invariant (printf "after deleting %s" (show r))
  let repPair (x, c) = do
        x' <- rep x
        return (x', c)
  funUses' <- mapM repPair funUses
  argUses' <- mapM repPair argUses

  m <- gets lookup

  let foldUses insert lookup pending m uses = foldl' op e uses
        where op (pending, newUses, m) (x', c) =
                case lookup x' m of
                  Just k -> ((c, k):pending, newUses, m)
                  Nothing -> (pending, (x', c):newUses, insert x' c m)
              e = (pending, [], m)

      (funPending, funNewUses, m') = foldUses (\x' c m -> insert2 x' r' c m)
                                              (\x' m -> lookup2 x' r' m)
                                              [] m funUses'

      (pending, argNewUses, argM) = foldUses IntMap.insert IntMap.lookup funPending
                                             (IntMap.findWithDefault IntMap.empty r' m')
                                             argUses'

  addFunUses funNewUses r'
  addArgUses argNewUses r'

  putLookup (if IntMap.null argM then m' else IntMap.insert r' argM m')
  invariant (printf "after updateUses (%s, %s)" (show r) (show r'))

  return pending

rep :: Int -> CC Int
rep s = liftUF (UF.rep s)

runCC :: S -> CC a -> (a, S)
runCC s m = runState m s

evalCC :: S -> CC a -> a
evalCC s m = fst (runCC s m)

execCC :: S -> CC a -> S
execCC s m = snd (runCC s m)

initial :: Int -> S
initial n = S IntMap.empty IntMap.empty IntMap.empty (UF.initial n)
