{-# LANGUAGE DeriveDataTypeable #-}
import Test.QuickCheck
import Prelude hiding (Left, Right)
import Control.Monad
import Data.Typeable
import QuickSpec

data Tree = Nil | Cons Tree Tree deriving (Eq, Ord, Typeable)
data Path = Top | Left Path Tree | Right Tree Path deriving (Eq, Ord)
data Zipper = Zipper Tree Path deriving (Eq, Ord, Typeable)

instance Arbitrary Zipper where
  arbitrary = liftM2 Zipper arbitrary arbitrary
instance CoArbitrary Zipper where
  coarbitrary (Zipper t p) = coarbitrary (t,p)
instance Arbitrary Tree where
  arbitrary =
    sized $ \n -> resize (n `div` 2) $
      oneof $
        [ return Nil ] ++
        [ liftM2 Cons arbitrary arbitrary | n > 0 ]
instance CoArbitrary Tree where
  coarbitrary Nil        = variant 0
  coarbitrary (Cons x y) = variant 1 . coarbitrary (x,y)
instance Arbitrary Path where
  arbitrary =
    sized $ \n -> resize (n `div` 2) $
      oneof $
        [ return Top ] ++
        [ liftM2 Left arbitrary arbitrary | n > 0 ] ++
        [ liftM2 Right arbitrary arbitrary | n > 0 ]
instance CoArbitrary Path where
  coarbitrary Top         = variant 0
  coarbitrary (Left  p t) = variant 1 . coarbitrary (p,t)
  coarbitrary (Right p t) = variant 2 . coarbitrary (p,t)

change :: Maybe Zipper -> Maybe Tree -> Maybe Zipper
change (Just (Zipper _ p)) (Just t) = Just (Zipper t p)
change _ _ = Nothing

upLeft, upRight, up, left, right :: Maybe Zipper -> Maybe Zipper
upLeft (Just (Zipper t (Right left father))) = Just (Zipper left (Left father t))
upLeft _ = Nothing
upRight (Just (Zipper t (Left father right))) = Just (Zipper right (Right t father))
upRight _ = Nothing
up (Just (Zipper t (Left father right))) = Just (Zipper (Cons t right) father)
up _ = Nothing
left (Just (Zipper (Cons left right) p)) = Just (Zipper left (Left p right))
left _ = Nothing
right (Just (Zipper (Cons left right) p)) = Just (Zipper right (Right right p))
right _ = Nothing

fromZipper :: Maybe Zipper -> Maybe Tree
fromZipper (Just (Zipper t p)) = Just (apply t p)
  where
    apply t Top = t
    apply t (Left p u) = apply (Cons t u) p
    apply t (Right u p) = apply (Cons u t) p
fromZipper _ = Nothing

toZipper :: Maybe Tree -> Maybe Zipper
toZipper (Just t) = Just (Zipper t Top)
toZipper _ = Nothing

sig =
  signature {
    constants = [
       constant "nothing" (Nothing :: Maybe A),
       constant "nil" Nil,
       constant "cons" Cons,
       constant "change" change,
       constant "up" up,
       constant "upLeft" upLeft,
       constant "upRight" upRight,
       constant "left" left,
       constant "right" right,
       constant "fromZipper" fromZipper,
       constant "toZipper" toZipper ],
    instances = [
      baseType (undefined :: Zipper),
      baseType (undefined :: Tree) ]}

main = quickSpec sig
