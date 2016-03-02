{-# LANGUAGE DeriveDataTypeable
           , GeneralizedNewtypeDeriving
  #-}
import Data.Maybe
import Data.List hiding ((//))
import Data.Char
import Test.QuickCheck hiding ((><))
import System.IO.Unsafe
import System.Timeout
import QuickSpec hiding (New, In, Name, Event)

--------------------------------------------------------------------------------

newtype Name
  = Name{ unName :: Char }
 deriving ( Eq, Ord, Enum, Typeable )

instance Show Name where
  show (Name a) = [a]

instance Arbitrary Name where
  arbitrary       = Name `fmap` growingElements ['a'..'d']
  shrink (Name a) = [ Name a' | a' <- ['a'..'d'], a' < a ]

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
  p `compare` q = p `unsafeCompare` q

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

bisim :: Int -> P -> P -> Bool
bisim k p q = steps k p == steps k q

--------------------------------------------------------------------------------

data WSteps
  = WStep [(Event,WSteps)] Bool
  | WStop
 deriving ( Eq, Ord, Show, Typeable )

wstep :: Int -> P -> ([(Event,P)],Bool)
wstep 0 _ = ([], False)
wstep n p = ([(e,q)|(e,q)<-eqs, e/= Tau] ++ concat eqs',done)
 where
  eqs          = step p
  (eqs',dones) = unzip [ wstep (n-1) q | (Tau,q) <- eqs ]
  done         = and dones

wsteps :: Int -> P -> WSteps
wsteps 0 _ = WStop
wsteps k p = WStep (usort [ (e,wsteps (k-1) q) | (e,q) <- eqs ]) done
 where
  (eqs,done) = wstep 100 p

p = New a
    (     Act (Out a) Nil
      :|: Star (Act (In a)
            ( Act (Out b) Nil
          :+: {- Act (Out c) -} (Act (Out a) Nil)
            ))
    )

p1 = Act (Out b) Nil
p2 = Star (Act Tau Nil)
p3 = Star (Act Tau (Act Tau (Act (Out a) Nil)))
p4 = Star (Act Tau (Act (Out a) Nil))

a = Name 'a'
b = Name 'b'
c = Name 'c'

--------------------------------------------------------------------------------

unsafeCompare :: P -> P -> Ordering
unsafeCompare p q =
  unsafePerformIO $
    do mres <- timeout 10000 (res `seq` return ())
       case mres of
         Nothing -> return EQ
         Just _  -> return res
 where
  h p = [ steps i p | i <- [2..7] ]
  res = p ~~ q

  p ~~ q =
    case (step p, step q) of
      ([], qs) | null qs   -> EQ
               | otherwise -> LT
      (ps, []) | null ps   -> EQ
               | otherwise -> GT
      ([(a,p')],[(b,q')])
               | a == b   -> p' ~~ q'
      _                   -> h p `compare` h q

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

prop_new_no a p =
  expectFailure $
    New a (p // a) == New a p

prop_star_new a p =
  expectFailure $
    Star (New a p) == New a (Star p)

prop_star_new2 a b p =
  expectFailure $
    Star (New a (New b p)) == New a (New b (Star p))

prop_star_tau_tau p =
  Star (p :+: Act Tau (Act Tau p)) == Star (p :+: Act Tau p)

prop_new_in_out a p q =
  New a (Act (In a) p :|: Act (Out a) q) == Act Tau (New a (p :|: q))

--testAll = $(quickCheckAll)

--------------------------------------------------------------------------------

newtype P_ = P_ P
 deriving ( Eq, Ord, Arbitrary, CoArbitrary, Typeable )

newtype Name_ = Name_ [Name]
 deriving ( Eq, Ord, CoArbitrary, Typeable )

instance Arbitrary Name_ where
  arbitrary =
    do a <- arbitrary
       b <- arbitrary `suchThat` (/=a)
       return (Name_ [a,b])

sig =
  signature
  { constants =
    -- Event
    [ -- con "in"  In
    -- , con "out" Out
    -- , con "tau" Tau
    
    -- Restricted processes
      con "/"    (\(P_ p) a -> p // a)
    
    -- Restricted names
    , con "#"    (\(Name_ as) b -> head (filter (/=b) as))
    
    -- P
    , con "0"    Nil
    -- , con "."    Act
    , con "?"    (Act . In)
    , con "!"    (Act . Out)
    , con "tau"  (Act Tau)
    , con "+"    (:+:)
    , con "|"    (:|:)
    , (con "*"   Star){ conStyle = Postfix }
    , con "new"  New
    ]
    
  , instances =
    [ baseTypeNames ["a","b","c"] (undefined :: Name)
    , baseTypeNames ["c"] (undefined :: Name_)
    -- , baseTypeNames ["e"]         (undefined :: Event)
    , baseTypeNames ["p","q","r"] (undefined :: P)
    , baseTypeNames ["r"] (undefined :: P_)
    ]
    
  , defaultTo = Just (typeOf (undefined :: Bool))
  }
 where
  con op f = constant op f

main = quickSpec sig
