{-# LANGUAGE DeriveDataTypeable, TypeOperators, StandaloneDeriving #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec hiding (background, (<>), text, nest, ($$))
import Text.PrettyPrint.HughesPJ

deriving instance Typeable Doc

instance Arbitrary Doc where
  arbitrary =
    sized $ \n ->
      let bin = resize (n `div` 2) arbitrary
          un = resize (n-1) arbitrary in
      oneof $
        [ liftM2 ($$) bin bin | n > 0 ] ++
        [ liftM2 (<>) bin bin | n > 0 ] ++
        [ liftM2 nest arbitrary un | n > 0 ] ++
        [ fmap text arbString ]

arbString :: Gen String
arbString = listOf (elements "ab")

background =
  signature {
    maxTermSize = Just 9,
    maxTests = Just 1000,
    constants = [
       constant "[]" ([] :: [A]),
       constant "++" ((++) :: [A] -> [A] -> [A]),
       constant "0" (0 :: Int),
       constant "+" ((+) :: Int -> Int -> Int),
       constant "length" (length :: String -> Int) ]}

-- obsDoc :: Doc -> Gen String
-- obsDoc d = do
--   n <- arbitrary
--   return (render (nest n d))

obsDoc :: Doc -> Gen String
obsDoc d = fmap render ctx
  where
    ctx =
      sized $ \n ->
      oneof $
        [ return d ] ++
        [ liftM2 op (resize (n `div` 2) ctx) (resize (n `div` 2) arbitrary) | n > 0, op <- [(<>), ($$)] ] ++
        [ liftM2 op (resize (n `div` 2) arbitrary) (resize (n `div` 2) ctx) | n > 0, op <- [(<>), ($$)] ] ++
        [ liftM2 nest arbitrary (resize (n-1) ctx) | n > 0 ]

unindented :: Doc -> Bool
unindented d = render (nest 100 (text "" <> d)) == render (nest 100 d)

nesting :: Doc -> Int
nesting d = head [ i | i <- nums, unindented (nest (-i) d) ]
  where
    nums = 0:concat [ [i, -i] | i <- [1..] ]

sig =
  signature {
    maxTests = Just 1000,
    constants = [
       constant "text" text,
       constant "nest" nest,
       --constant "nesting" nesting,
       constant "<>" (<>),
       constant "$$" ($$) ],
    instances = [
      makeInstance (\() -> arbString),
      makeInstance (\() -> observe obsDoc),
      inst (Sub Dict :: () :- Arbitrary Doc) ],
    defaultTo = Just (typeOf (undefined :: Bool)) }

main = quickSpecWithBackground background sig
