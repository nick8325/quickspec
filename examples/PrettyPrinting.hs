-- Pretty-printing combinators.
-- Illustrates observational equality.
-- See the QuickSpec paper for more details.
{-# LANGUAGE DeriveDataTypeable, TypeOperators, StandaloneDeriving #-}
import Control.Monad
import Test.QuickCheck
import QuickSpec
import Text.PrettyPrint.HughesPJ
import Data.Proxy
import Data.Constraint

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

-- Observational equality.
obsDoc :: Context -> Doc -> String
obsDoc (Context ctx) d = render (ctx d)

newtype Context = Context (Doc -> Doc)

instance Arbitrary Context where
  arbitrary = Context <$> ctx
    where
      ctx =
        sized $ \n ->
        oneof $
          [ return id ] ++
          [ liftM2 (\x y d -> op (x d) y) (resize (n `div` 2) ctx) (resize (n `div` 2) arbitrary) | n > 0, op <- [(<>), ($$)] ] ++
          [ liftM2 (\x y d -> op x (y d)) (resize (n `div` 2) arbitrary) (resize (n `div` 2) ctx) | n > 0, op <- [(<>), ($$)] ] ++
          [ liftM2 (\x y d -> nest x (y d)) arbitrary (resize (n-1) ctx) | n > 0 ]

unindented :: Doc -> Bool
unindented d = render (nest 100 (text "" <> d)) == render (nest 100 d)

nesting :: Doc -> Int
nesting d = head [ i | i <- nums, unindented (nest (-i) d) ]
  where
    nums = 0:concat [ [i, -i] | i <- [1..] ]

main = quickSpec [
  withMaxTermSize 9,
  
  background [
    con "[]" ([] :: [A]),
    con "++" ((++) :: [A] -> [A] -> [A]),
    con "0" (0 :: Int),
    con "+" ((+) :: Int -> Int -> Int),
    con "length" (length :: [A] -> Int) ],


  con "text" text,
  con "nest" nest,
  --con "nesting" nesting,
  con "<>" (<>),
  con "$$" ($$),

  inst arbString,
  inst (\gen -> observe gen obsDoc),
  inst (Sub Dict :: () :- Arbitrary Doc),
  inst (Sub Dict :: () :- Arbitrary Context),
  defaultTo (Proxy :: Proxy Bool)]
