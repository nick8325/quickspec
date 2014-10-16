{-# LANGUAGE DeriveDataTypeable
           , GeneralizedNewtypeDeriving
  #-}
module Process where

import Data.Maybe
import Data.List hiding ((//))
import Data.Char
import Test.QuickCheck hiding ((><))
import Data.Typeable

--------------------------------------------------------------------------------

newtype Name
  = Name{ unName :: Char }
 deriving ( Eq, Ord, Enum, Typeable )

(#) :: Name -> Name -> Name
Name a # Name b | a == b    = Name (succ a)
                | otherwise = Name a

instance Show Name where
  show (Name a) = [a]

instance Arbitrary Name where
  arbitrary       = Name `fmap` growingElements ['a'..'c']
  shrink (Name a) = [ Name a' | a' <- ['a'..'c'], a' < a ]

instance CoArbitrary Name where
  coarbitrary n = coarbitrary (show n)

--------------------------------------------------------------------------------

data Event
  = In Name
  | Out Name
  | Tau
 deriving ( Eq, Ord, Typeable )

(><) :: Event -> Event -> Bool
In a  >< Out b = a == b
Out a >< In b  = a == b
_     >< _     = False

has :: Event -> Name -> Bool
In a  `has` b = a == b
Out a `has` b = a == b
_     `has` _ = False

instance Show Event where
  show (In  a) = show a ++ "?"
  show (Out a) = show a ++ "!"
  show Tau     = "τ"

instance Arbitrary Event where
  arbitrary =
    frequency
    [ (1, In  `fmap` arbitrary)
    , (1, Out `fmap` arbitrary)
    , (1, return Tau)
    ]

  shrink Tau     = []
  shrink (In a)  = [ Tau, Out a ]
                ++ [ In a' | a' <- shrink a ]
  shrink (Out a) = [ Tau ]
                ++ [ Out a' | a' <- shrink a ]

instance CoArbitrary Event where
  coarbitrary e = coarbitrary (show e)

--------------------------------------------------------------------------------

data P
  = Nil
  | Act Event P
  | P :+: P
  | P :|: P
  | Star P
  | New Name P
 deriving ( Typeable )

instance Eq P where
  p == q = (p `compare` q) == EQ

instance Ord P where
  p `compare` q = steps 4 p `compare` steps 4 q

instance Show P where
  show Nil       = "0"
  show (Act m p) = show m ++ show p
  show (p :+: q) = "(" ++ show p ++ "+" ++ show q ++ ")"
  show (p :|: q) = "(" ++ show p ++ "|" ++ show q ++ ")"
  show (Star p)  = "(" ++ show p ++ ")*"
  show (New a p) = "(new " ++ show a ++ "." ++ show p ++ ")"

instance Arbitrary P where
  arbitrary = sized arbP
   where
    arbP n =
      frequency
      [ (1, do return Nil)
      , (k, do e <- arbitrary
               p <- arbP (n-1)
               return (Act e p))
      , (k, do p <- arbP (n`div`2)
               q <- arbP (n`div`2)
               return (p:+:q))
      , (k, do p <- arbP (n`div`2)
               q <- arbP (n`div`2)
               return (p:|:q))
      {-
      , (k, do p <- arbP (n`div`2)
               return (Star p))
      -}
      , (k, do a <- arbitrary
               p <- arbP (n`div`2)
               return (New a p))
      ]
     where
      k = 3 `min` n

  shrink Nil       = []
  shrink (Act e p) = [ p ]
                  ++ [ Act e' p | e' <- shrink e ]
                  ++ [ Act e p' | p' <- shrink p ]
  shrink (p :+: q) = [ p, q ]
                  ++ [ p' :+: q | p' <- shrink p ]
                  ++ [ p :+: q' | q' <- shrink q ]
  shrink (p :|: q) = [ p, q, p :+: q ]
                  ++ [ p' :|: q | p' <- shrink p ]
                  ++ [ p :|: q' | q' <- shrink q ]
  shrink (Star p)  = [ p, p :|: p, p :|: (p :|: p) ]
                  ++ [ Star p' | p' <- shrink p ]
  shrink (New a p) = [ p ]
                  ++ [ New a' p | a' <- shrink a ]
                  ++ [ New a p' | p' <- shrink p ]
                  
instance CoArbitrary P where
  coarbitrary p = coarbitrary (show p)

(//) :: P -> Name -> P
p // a | p `hasp` a = Nil
       | otherwise  = p
 where
  Nil       `hasp` a = False
  Act e p   `hasp` a = e `has` a || p `hasp` a
  (p :+: q) `hasp` a = p `hasp` a || q `hasp` a
  (p :|: q) `hasp` a = p `hasp` a || q `hasp` a
  Star p    `hasp` a = p `hasp` a
  New b p   `hasp` a
    | a == b         = False
    | otherwise      = p `hasp` a

--------------------------------------------------------------------------------

step :: P -> [(Event, P)]
step Nil =
  []

step (Act e p) =
  [(e, p)]

step (p :+: q) =
  step p ++ step q

step (p :|: q) =
  [ (Tau, p' :|: q')
  | (a, p') <- ps
  , (b, q') <- qs
  , a >< b
  ] ++
  [ (e, p' :|: q)
  | (e, p') <- ps
  ] ++
  [ (e, p :|: q')
  | (e, q') <- qs
  ]
 where
  ps = step p
  qs = step q

step (Star p) =
  [ (e, p' :|: Star p)
  | (e, p') <- step p
  ] ++
  [ (Tau, (p1 :|: p2) :|: Star p)
  | (a, p1) <- step p
  , (b, p2) <- step p
  , a >< b
  , a < b
  ]

step (New a p) =
  [ (e, New a p')
  | (e, p') <- step p
  , not (e `has` a)
  ]

--------------------------------------------------------------------------------

data Steps
  = Step [(Event,Steps)]
  | Stop
 deriving ( Eq, Ord, Show, Typeable )

steps :: Int -> P -> Steps
steps 0 _ = Stop
steps k p = Step (usort [ (a, steps (k-1) q) | (a,q) <- step p ])

usort :: Ord a => [a] -> [a]
usort = map head . group . sort

bisim :: Int -> P -> P -> Bool
bisim k p q = steps k p == steps k q

--------------------------------------------------------------------------------

{-
sig :: [Sig]
sig =
  -- Name
  [ ["A","B"] `vars` (undefined :: Name)
  , "#" `fun2` (#)
  , "a" `fun0` Name 'a'
  , "b" `fun0` Name 'b'
  
  -- Event
  , ["E","D"] `vars` (undefined :: Event)
  , "?" `fun1` In
  , "!" `fun1` Out
  , "τ" `fun0` Tau
  
  -- P
  , ["P","Q","R"] `vars` (undefined :: P)
  , background [
      "0"   `fun0` Nil
    , "."   `fun2` Act
    , "+"   `fun2` (:+:)
    , "|"   `fun2` (:|:)
    , "*"   `fun1` Star
    ]
  , "new" `fun2` New
  , "/"   `fun2` (//)
  ]

main :: IO ()
main = quickSpec sig
-}

--------------------------------------------------------------------------------

(~~) :: P -> P -> Bool
p ~~ q = bisim 5 p q

prop_new_no a p =
  expectFailure $
    New a (p // a) ~~ New a p

--testAll = $(quickCheckAll)

--------------------------------------------------------------------------------

