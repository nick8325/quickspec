-- A window manager example,
-- taken from http://donsbot.wordpress.com/2007/05/01/roll-your-own-window-manager-part-1-defining-and-testing-a-model

import Data.Maybe
import Data.Map (Map)
import Data.Typeable
import qualified Data.Map as M
import qualified Data.List as L
import Test.QuickCheck
import Test.QuickCheck.Instances
import Test.QuickCheck.Poly(OrdA)
import QuickSpec
import Numeric.Natural

-- ---------------------------------------------------------------------
-- A data structure for multiple workspaces containing stacks of screens
--

data StackSet a = StackSet
    { current :: Natural           -- the current workspace
    , stacks  :: Map Natural [a] } -- map workspaces to window stacks
    deriving (Eq, Ord, Show, Read, Typeable)

-- | /O(n)/. Create a new empty stackset of 'n' workspaces
empty :: Ord a => Natural -> StackSet a
empty n = StackSet { current = 0, stacks  = ws }
  where
    ws = M.fromList (zip [0..n-1] (repeat []))

-- | /O(log n)/. Set the given stack as being visible. If the index is out of
-- bounds, the stack is returned unmodified.
view :: Natural -> StackSet a -> StackSet a
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
shift :: (Ord a) => Natural -> StackSet a -> StackSet a
shift n w = maybe w (\k -> insert k n w) (peek w)

-- | /O(log n)/. Insert an element onto the top of stack 'n'.
-- If the element is already in the stack 'n', it is moved to the top.
-- If the element exists on another stack, it is removed from that stack.
-- If the index is wrong an exception is thrown.
insert :: Ord a => a -> Natural -> StackSet a -> StackSet a
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
index :: Natural -> StackSet a -> [a]
index k w = fromJust (M.lookup k (stacks w))

--
-- Arbitrary instances and helper functions.
--

------------------------------------------------------------------------
--
-- Building StackSets from lists
--

fromList :: Ord a => (Natural, [[a]]) -> StackSet a
fromList (_,[]) = error "Cannot build a StackSet from an empty list"
fromList (n,xs) | n < 0 || n >= fromIntegral (length xs)
                = error $ "Cursor index is out of range: " ++ show (n, length xs)
fromList (o,xs) = view o $
    foldr (\(i,ys) s ->
        foldr (\a t -> insert a i t) s ys)
            (empty (fromIntegral (length xs))) (zip [0..] xs)

-- flatten a stackset to a list
toList  :: StackSet a -> (Natural,[[a]])
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
size :: T -> Natural
size = fromIntegral . M.size . stacks

-- | Height of stack 'n'
height :: Natural -> T -> Natural
height i w = fromIntegral (length (index i w))

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

type T = StackSet OrdA

ordering :: Sig
ordering = signature [
  con "LT" LT,
  con "GT" GT,
  con "EQ" EQ,
  monoTypeWithVars ["o", "o'"] (Proxy :: Proxy Ordering)]

tinywm :: [Sig]
tinywm = [
  prelude `without` ["+", "*"],
  arith (Proxy :: Proxy Natural),
  ordering,

  monoTypeWithVars ["s"] (Proxy :: Proxy T),

  "empty"   `con` (empty           :: Natural -> T),
  "view"    `con` (view            :: Natural -> T -> T),
  "peek"    `con` (fromJust . peek :: T -> OrdA),
  "rotate"  `con` (rotate          :: Ordering -> T -> T),
  "push"    `con` (push            :: OrdA -> T -> T),
  "shift"   `con` (shift           :: Natural -> T -> T),
  "insert"  `con` (insert          :: OrdA -> Natural -> T -> T),
  "delete"  `con` (delete          :: OrdA -> T -> T),
  "current" `con` (current         :: T -> Natural),
  "index"   `con` (index           :: Natural -> T -> [OrdA])]

main = quickSpec tinywm
