-- A simple process calculus.
{-# LANGUAGE DeriveDataTypeable
           , GeneralizedNewtypeDeriving
           , DeriveGeneric
           , TypeApplications
           , FlexibleInstances
           , MultiParamTypeClasses
           , DeriveFunctor
  #-}
import Data.Maybe
import Data.List hiding ((//))
import Data.Char
import Test.QuickCheck hiding ((><), Result)
import System.IO.Unsafe
import System.Timeout
import QuickSpec
import QuickSpec.Internal
import QuickSpec.Internal.Utils
import Data.Proxy
import GHC.Generics
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Ord
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad

--------------------------------------------------------------------------------

newtype Name
  = Name{ unName :: Char }
 deriving ( Eq, Ord, Enum, Typeable )

instance Show Name where
  show (Name a) = [a]

instance Arbitrary Name where
  arbitrary       = Name `fmap` growingElements domain
  shrink (Name a) = [ Name a' | a' <- domain, a' < a ]

domain :: [Char]
domain = ['a'..'c']

a = Name 'a'
b = Name 'b'
c = Name 'c'
d = Name 'd'

instance CoArbitrary Name where
  coarbitrary n = coarbitrary (show n)

--------------------------------------------------------------------------------

type Event = Name

--------------------------------------------------------------------------------

data P
  = Nil
  | Act Event P
  | Sync (Set Event) P P
  | Choice P P
  | Nondet P P
  | Interrupt P P
 deriving ( Typeable, Generic )

instance Observe Int Steps P where
  observe n p = steps (min (abs n) 5) p

-- Doesn't use observational equality!

instance Show P where
  show Nil       = "0"
  show (Act m p) = show m ++ "." ++ show p
  show (Sync es p q)
    | Set.null es = "(" ++ show p ++ "|" ++ show q ++ ")"
    | otherwise = show (Set.toList es) ++ "(" ++ show p ++ "|" ++ show q ++ ")"
  show (Choice p q) = "(" ++ show p ++ "□" ++ show q ++ ")"
  show (Nondet p q) = "(" ++ show p ++ "?" ++ show q ++ ")"
  show (Interrupt p q) = "(" ++ show p ++ "/_\\" ++ show q ++ ")"

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
               es <- arbitrary
               return (Sync es p q))
      , (k, do p <- arbP (n`div`2)
               q <- arbP (n`div`2)
               return (Choice p q))
      , (k, do p <- arbP (n`div`2)
               q <- arbP (n`div`2)
               return (Nondet p q))
      , (k, do p <- arbP (n`div`2)
               q <- arbP (n`div`2)
               return (Interrupt p q))
      ]
     where
      k = 3 `min` n

  shrink = genericShrink
                  
instance CoArbitrary P where
  coarbitrary p = coarbitrary (show p)

happy :: Set Event -> P
happy es =
  foldr (Sync Set.empty) Nil
    [Act e (happy es) | e <- Set.toList es]

--------------------------------------------------------------------------------

alphabet :: P -> Set Event
alphabet Nil = Set.empty
alphabet (Act e p) = Set.insert e (alphabet p)
alphabet (Sync _ p q) = alphabet p `Set.union` alphabet q
alphabet (Choice p q) = alphabet p `Set.union` alphabet q
alphabet (Nondet p q) = alphabet p `Set.union` alphabet q
alphabet (Interrupt p q) = alphabet p `Set.union` alphabet q

step :: P -> (Set Event, Map Event [P])
step Nil = (Set.empty, Map.empty)

step (Act e p) = (Set.singleton e, Map.singleton e [p])

step (Sync es p q) =
  ((ep `Set.difference` es) `Set.union`
   (eq `Set.difference` es) `Set.union`
   (ep `Set.intersection` eq `Set.intersection` es),
   Map.unionsWith (++) $
     [Map.intersectionWith (liftM2 (\p' q' -> Sync es p' q')) p1 q1,
      Map.map (map (\p' -> Sync es p' q)) p2,
      Map.map (map (\q' -> Sync es p q')) q2])
  where
    (ep, sp) = step p
    (eq, sq) = step q
    p1 = Map.restrictKeys sp es
    p2 = Map.withoutKeys  sp es
    q1 = Map.restrictKeys sq es
    q2 = Map.withoutKeys  sq es

step (Choice p q) =
  (ep `Set.union` eq,
   Map.unionWith (++) sp sq)
  where
    (ep, sp) = step p
    (eq, sq) = step q

step (Nondet p q) =
  (ep `Set.intersection` eq,
   Map.unionWith (++) sp sq)
  where
    (ep, sp) = step p
    (eq, sq) = step q

step (Interrupt p q) =
  (ep `Set.union` eq,
   Map.unionWith (++) (Map.map (map (\p -> Interrupt p q)) sp) sq)
  where
    (ep, sp) = step p
    (eq, sq) = step q

--------------------------------------------------------------------------------

data Steps = Step (Set Event) (Map Event Steps) | Stop
  deriving (Eq, Ord, Show)

steps :: Int -> P -> Steps
steps 0 _ = Stop
steps n p = Step end (Map.fromListWith combine [ (a, steps (n-1) q) | (a,qs) <- Map.toList s, q <- qs ])
  where
    (end, s) = step p
    combine (Step s1 m1) (Step s2 m2) = Step (s1 `Set.intersection` s2) (Map.unionWith combine m1 m2)
    combine Stop _ = Stop
    combine _ Stop = Stop

data After a = Failed | May a | Will a
  deriving (Eq, Ord, Show, Functor)

isWill (Will _) = True
isWill _ = False

the Failed = Nothing
the (May x) = Just x
the (Will x) = Just x

after :: [Event] -> P -> After P
after es p =
  case follow es p of
    Failed -> Failed
    May ps -> May (combine ps)
    Will ps -> Will (combine ps)
  where
    combine = foldr1 Nondet
    union (Step e1 s1) (Step e2 s2) =
      Step (e1 `Set.intersection` e2) (Map.unionWith union s1 s2)
    union _ Stop = Stop
    union Stop _ = Stop

    follow :: [Event] -> P -> After [P]
    follow [] p = Will [p]
    follow (e:es) p =
      downgrade $
      collect $
      case Map.lookup e next of
        Nothing -> []
        Just qs -> map (follow es) qs
      where
        (end, next) = step p
        downgrade :: After a -> After a
        downgrade (Will x)
          | e `Set.notMember` end = May x
        downgrade x = x
        collect :: [After [p]] -> After [p]
        collect [] = Failed
        collect xs
          | all isWill xs = Will (concat (map (fromJust . the) xs))
          | otherwise =
            case catMaybes (map the xs) of
              [] -> Failed
              ys -> May (concat ys)

data Primed = Primed P [Event] deriving Show

instance Arbitrary Primed where
  arbitrary =
    frequency
      [(3, liftM2 Primed arbitrary (return []))]

primed :: P -> Primed
primed p = Primed p []

(//) :: Primed -> [Event] -> Primed
Primed p es // fs = Primed p (es ++ fs)

instance Observe Int (After Steps) Primed where
  observe n (Primed p es) = fmap (steps n) (after es p)

main = quickSpec [
  withMaxTests 1000,
  withMaxTermSize 7,
  lists,
  background [
    con "∅" (Set.empty @Name),
    con "∪" (Set.union @Name)],
--    con "True" True, con "False" False, con "&&" (&&),
--    con "unit" (Set.singleton @Name)],
--    --predicate "∈" (Set.member @Name)],

  -- P
  series [
    --[con "alphabet" alphabet],
    [con "0"    Nil],
  --  [con "menu" menu],
  --  [con "restrict1" restrict1],
    --[con "|"    (\p q -> Sync Set.empty p q)],
    [con "|"    (Sync Set.empty)],
    [con "sync" (Sync . Set.singleton)],
    [con "□"    Choice],
    [con "⊓"    Nondet],
    [con "."    Act],
    [con "/_\\" Interrupt]]
    --[con "happy" happy]]

    --[con "primed" primed,
    -- con "//" (\p x -> p // [x])]]
  
  , instFun (take 3 <$> arbitrary :: Gen [Event])
  , monoTypeWithVars ["a","b","c"] (Proxy :: Proxy Name)
  , monoTypeObserveWithVars ["p","q","r"] (Proxy :: Proxy P)
  , monoTypeObserveWithVars ["p","q","r"] (Proxy :: Proxy Primed)
  , monoTypeWithVars ["as","bs","cs"] (Proxy :: Proxy (Set Name))]
