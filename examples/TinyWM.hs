-- A window manager example,
-- taken from http://donsbot.wordpress.com/2007/05/01/roll-your-own-window-manager-part-1-defining-and-testing-a-model

{-# OPTIONS -fglasgow-exts #-}

import Data.Maybe
import Data.Map (Map)
import Data.Typeable
import qualified Data.Map as M
import qualified Data.List as L
import Test.QuickCheck
import Test.QuickSpec

-- ---------------------------------------------------------------------
-- A data structure for multiple workspaces containing stacks of screens
--

data StackSet a = StackSet
    { current :: Int           -- the current workspace
    , stacks  :: Map Int [a] } -- map workspaces to window stacks
    deriving (Eq, Ord, Show, Read, Typeable)

-- | /O(n)/. Create a new empty stackset of 'n' workspaces
empty :: Ord a => Int -> StackSet a
empty n = StackSet { current = 0, stacks  = ws }
  where
    ws = M.fromList (zip [0..n-1] (repeat []))

-- | /O(log n)/. Set the given stack as being visible. If the index is out of
-- bounds, the stack is returned unmodified.
view :: Int -> StackSet a -> StackSet a
view n w | M.member n (stacks w) = w { current = n }
         | otherwise             = w

-- | /O(log s)/. Extract the element on the top of the current stack.
-- If no such element exists, Nothing is returned.
peek :: Ord a => StackSet a -> Maybe a
peek w | Just (x:_) <- M.lookup (current w) (stacks w) = Just x
       | otherwise                                     = Nothing

-- | /O(log n)/. rotate. cycle the current window list up or down.
-- Has the effect of rotating focus. In fullscreen mode this will cause
-- a new window to be visible.
--
--  rotate EQ   -->  [5,6,7,8,1,2,3,4]
--  rotate GT   -->  [6,7,8,1,2,3,4,5]
--  rotate LT   -->  [4,5,6,7,8,1,2,3]
--
--  where xs = [5..8] ++ [1..4]
--
rotate :: Ordering -> StackSet a -> StackSet a
rotate o w = w { stacks = M.adjust rot (current w) (stacks w) }
  where
    rot [] = []
    rot xs = case o of
        GT -> tail xs ++ [head xs]
        LT -> last xs : init xs
        _  -> xs

-- ---------------------------------------------------------------------
-- operations that affect multiple workspaces

-- | /O(log n)/. Push. Insert an element onto the top of the current stack.
-- If the element is already in the current stack, it is moved to the top.
-- If the element is managed on another stack, it is removed from that stack.
--
push :: Ord a => a -> StackSet a -> StackSet a
push k w = insert k (current w) w

-- | /O(log n)/. shift. move the client on top of the current stack to
-- the top of stack 'n'. If the stack to move to is not valid, and
-- exception is thrown. If there's no client on the current stack, the
-- stack set is returned unchanged.
shift :: (Ord a) => Int -> StackSet a -> StackSet a
shift n w = maybe w (\k -> insert k n w) (peek w)

-- | /O(log n)/. Insert an element onto the top of stack 'n'.
-- If the element is already in the stack 'n', it is moved to the top.
-- If the element exists on another stack, it is removed from that stack.
-- If the index is wrong an exception is thrown.
insert :: Ord a => a -> Int -> StackSet a -> StackSet a
insert k n old = new { stacks = M.adjust (k:) n (stacks new) }
    where new = delete k old

-- | /O(n)/. Delete an element entirely from from the StackSet.
-- If the element doesn't exist, the original StackSet is returned unmodified.
-- If the current element is focused, focus will change.
delete :: Ord a => a -> StackSet a -> StackSet a
delete k w = maybe w del $ L.find ((k `elem`) . snd) (M.assocs (stacks w))
  where
    del (i,_) = w { stacks = M.adjust (L.delete k) i (stacks w) }

-- | /O(log n)/. Index. Extract the stack at workspace 'n'.
-- If the index is invalid, an exception is thrown.
index :: Int -> StackSet a -> [a]
index k w = fromJust (M.lookup k (stacks w))

--
-- Arbitrary instances and helper functions.
--

------------------------------------------------------------------------
--
-- Building StackSets from lists
--

fromList :: Ord a => (Int, [[a]]) -> StackSet a
fromList (_,[]) = error "Cannot build a StackSet from an empty list"
fromList (n,xs) | n < 0 || n >= length xs
                = error $ "Cursor index is out of range: " ++ show (n, length xs)
fromList (o,xs) = view o $
    foldr (\(i,ys) s ->
        foldr (\a t -> insert a i t) s ys)
            (empty (length xs)) (zip [0..] xs)

-- flatten a stackset to a list
toList  :: StackSet a -> (Int,[[a]])
toList x = (current x, map snd $ M.toList (stacks x))

-- ---------------------------------------------------------------------
--
-- Some useful predicates and helpers
--

-- a window is a member
member :: Ord a => a -> StackSet a -> Bool
member k w =
    case L.find ((k `elem`) . snd) (M.assocs (stacks w)) of
        Nothing -> False
        _       -> True

-- | /O(n)/. Number of stacks
size :: T -> Int
size = M.size . stacks

-- | Height of stack 'n'
height :: Int -> T -> Int
height i w = length (index i w)

--
-- Generate arbitrary stacksets
--
instance (Ord a, Arbitrary a) => Arbitrary (StackSet a) where
    arbitrary = do
        sz <- choose (1,5)
        n  <- choose (0,sz-1)
        ls <- vector sz
        let s = fromList (fromIntegral n,ls)
        return s

instance (Ord a, CoArbitrary a) => CoArbitrary (StackSet a) where
    coarbitrary s = coarbitrary (toList s)

--
-- QuickSpec stuff.
--

ordering :: Sig
ordering = signature [
  con "LT" LT,
  con "GT" GT,
  con "EQ" EQ,
  vars ["o", "o'"] (undefined :: Ordering)]

--
-- constrain it to a simple element type
--
type T = StackSet A

tinywm :: [Sig]
tinywm = [
  prelude (undefined :: A) `without` ["+", "*"],
  gvars ["x", "y", "q"] (choose (0, 3) :: Gen Int),
  ordering,

  ["s"] `vars` (undefined :: T),

  "empty"   `fun1` (empty           :: Int -> T),
  "view"    `fun2` (view            :: Int -> T -> T),
  "peek"    `fun1` (fromJust . peek :: T -> A),
  "rotate"  `fun2` (rotate          :: Ordering -> T -> T),
  "push"    `fun2` (push            :: A -> T -> T),
  "shift"   `fun2` (shift           :: Int -> T -> T),
  "insert"  `fun3` (insert          :: A -> Int -> T -> T),
  "delete"  `fun2` (delete          :: A -> T -> T),
  "current" `fun1` (current         :: T -> Int),
  "index"   `fun2` (index           :: Int -> T -> [A])]

main = quickSpec tinywm
