-- Pretty-printing combinators.
-- Illustrates observational equality and using custom generators.
-- See the QuickSpec paper for more details.
{-# LANGUAGE DeriveDataTypeable, TypeOperators, StandaloneDeriving, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
import Prelude hiding ((<>), (<$>))
import Control.Monad
import Test.QuickCheck
import QuickSpec
import QuickSpec.Internal(instFun)
import Text.PrettyPrint.ANSI.Leijen hiding (Str)
import Data.Proxy
import Data.Constraint

deriving instance Typeable Doc

instance Arbitrary Doc where
  arbitrary =
    sized $ \n ->
      let bin = resize (n `div` 2) arbitrary
          un = resize (n-1) arbitrary
          op = elements [(<>), (<$>), (</>), (<$$>), (<//>), (<+>)] in
      oneof $
        [ liftM3 id op bin bin | n > 0 ] ++
        [ liftM2 nest arbitrary un | n > 0 ] ++
        [ elements [line, linebreak, softline, softbreak, hardline ]] ++
        [ fmap group un | n > 0 ] ++
        [ fmap text (fmap (filter (/= '\n')) arbitrary) ]

-- Observational equality.
instance Observe (Context, Float, Int) String Doc where
  observe (Context ctx, f, n) d =
    displayS (renderPretty f n (ctx d)) ""

newtype Context = Context (Doc -> Doc)

instance Arbitrary Context where
  arbitrary = fmap Context ctx
    where
      ctx =
        sized $ \n ->
        oneof $
          [ return id ] ++
          [ liftM2 (\x y d -> op (x d) y) (resize (n `div` 2) ctx) (resize (n `div` 2) arbitrary) | n > 0, op <- [(<>), (<+>), (<$>), (</>), (<$$>), (<//>)] ] ++
          [ liftM2 (\x y d -> op x (y d)) (resize (n `div` 2) arbitrary) (resize (n `div` 2) ctx) | n > 0, op <- [(<>), (<+>), (<$>), (</>), (<$$>), (<//>)] ] ++
          [ fmap (group .) (resize (n-1) ctx) | n > 0 ] ++
          [ liftM2 (\x y d -> nest x (y d)) (fmap abs arbitrary) (resize (n-1) ctx) | n > 0 ]

--unindented :: Doc -> Bool
--unindented d = render (nest 100 (text "" <> d)) == render (nest 100 d)
--
--nesting :: Doc -> Int
--nesting d = head [ i | i <- nums, unindented (nest (-i) d) ]
--  where
--    nums = 0:concat [ [i, -i] | i <- [1..] ]

main = quickSpec [
  withMaxTermSize 9,
  
  background [
    con "[]" ([] :: [A]),
    con "++" ((++) :: [A] -> [A] -> [A]),
    con "0" (0 :: Int),
    con "+" ((+) :: Int -> Int -> Int),
    con "length" (length :: [A] -> Int) ],

  series [
    [con "text" text,
     con "nest" nest,
     --con "nesting" nesting,
     con "<>" ((<>) :: Doc -> Doc -> Doc),
     con "<$>" (<$>),
     con "</>" (</>),
--     con "<$$>" (<$$>),
--     con "<//>" (<//>),
     con "<+>" (<+>)],
    [con "group" group],
    [con "line" line,
--     con "linebreak" linebreak,
--     con "softline" softline,
--     con "softbreak" softbreak,
     con "hardline" hardline]],

  instFun (fmap (filter (/= '\n')) arbitrary :: Gen String),
  instFun (fmap abs arbitrary :: Gen Int),
  instFun (choose (0, 1) :: Gen Double),

  monoTypeObserve (Proxy :: Proxy Doc),
  defaultTo (Proxy :: Proxy Bool)]
