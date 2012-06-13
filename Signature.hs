{-# LANGUAGE ExistentialQuantification, StandaloneDeriving, DeriveDataTypeable #-}
module Signature where

import Control.Applicative hiding (some)
import Data.Typeable
import Data.Monoid
import Test.QuickCheck
import Term
import Typed
import Data.List
import qualified Data.Map as Map
import Utils

deriving instance Typeable1 Gen

class Signature a where
  toSig :: a -> Sig

instance Signature Sig where
  toSig = id

instance Signature a => Signature [a] where
  toSig = mconcat . map toSig

data Sig = Sig {
  constants :: TypeMap (C [] (C Named Value)),
  variables :: TypeMap (C [] (C Named Gen)),
  observers :: TypeMap Observer,
  ords :: TypeMap Observer
  }

names :: TypeMap (C [] (C Named f)) -> [Name]
names = concatMap (some (map (erase . unC) . unC)) . Map.elems

types :: Sig -> [TypeRep]
types sig = usort (map typ_ (names (constants sig)) ++ map typ_ (names (variables sig)))

instance Show Sig where show = unlines . summarise

summarise :: Sig -> [String]
summarise sig =
  [ "-- functions --" ] ++ describe constants ++
  [ "", "-- variables --" ] ++ describe variables ++
  concat
  [ [ "", "** the following types are using non-standard equality **" ] ++
    map show (Map.keys (observers sig))
  | not (Map.null (observers sig)) ]
  where
    describe f =
      [ intercalate ", " (map name xs) ++ " :: " ++ show (typ_ x) 
      | xs@(x:_) <- partitionBy typ_ (names (f sig)) ]

data Observer a = forall b. Ord b => Observer (Gen (a -> b)) deriving Typeable

emptySig :: Sig
emptySig = Sig Typed.empty Typed.empty Typed.empty Typed.empty

instance Monoid Sig where
  mempty = emptySig
  s1 `mappend` s2 =
    Sig {
      constants = renumber 0 constants',
      variables = renumber (length constants') variables',
      observers = observers s1 <> observers s2,
      ords = ords s1 <> ords s2 }
    where constants' = constants s1 `jumble` constants s2
          variables' = variables s1 `jumble` variables s2
          jumble x y =
            concatMap (\(Some (C xs)) -> map Some xs) $
            Typed.toList x ++ Typed.toList y
  
          renumber n =
            Typed.fromList .
            Typed.classify .
            zipWith (\i -> mapSome (alter i)) [n..]
          
          alter n (C x) = C x { index = n }

constantSig :: Typeable a => Named (Value a) -> Sig
constantSig x = emptySig { constants = Typed.fromList [Some (C [C x])] }

variableSig :: Typeable a => Named (Gen a) -> Sig
variableSig x = emptySig { variables = Typed.fromList [Some (C [C x])] }

observerSig :: Typeable a => Observer a -> Sig
observerSig x = emptySig { observers = Typed.fromList [Some x] }

ordSig :: Typeable a => Observer a -> Sig
ordSig x = emptySig { ords = Typed.fromList [Some x] }

blind :: Typeable a => String -> a -> Sig
blind x f = constantSig (Named 0 x (typeOf f) (Value f))

ord :: (Ord a, Typeable a) => a -> Sig
ord x = ordSig (Observer (return id) `observing` x)

observing :: Observer a -> a -> Observer a
observing x _ = x

vars :: (Arbitrary a, Typeable a) => [String] -> a -> Sig
vars xs v = mconcat [ var x v | x <- xs ]

var :: (Arbitrary a, Typeable a) => String -> a -> Sig
var x v = variableSig (Named 0 x (typeOf v) (arbitrary `asTypeOf` return v))

con, fun0 :: (Ord a, Typeable a) => String -> a -> Sig
con = fun0
fun0 x f = blind x f <> ord f

fun1 :: (Typeable a,
         Typeable b, Ord b) =>
        String -> (a -> b) -> Sig
fun1 x f = blind x f <> ord (f undefined)

fun2 :: (Typeable a, Typeable b,
         Typeable c, Ord c) =>
        String -> (a -> b -> c) -> Sig
fun2 x f = blind x f <>
           ord (f undefined undefined)

fun3 :: (Typeable a, Typeable b, Typeable c,
         Typeable d, Ord d) =>
        String -> (a -> b -> c -> d) -> Sig
fun3 x f = blind x f <>
           ord (f undefined undefined undefined)

fun4 :: (Typeable a, Typeable b, Typeable c, Typeable d,
         Typeable e, Ord e) =>
        String -> (a -> b -> c -> d -> e) -> Sig
fun4 x f = blind x f <>
           ord (f undefined undefined undefined undefined)

observer1 :: (Typeable a, Typeable b, Ord b) => (a -> b) -> Sig
observer1 f = observerSig (Observer (return f))

observer2 :: (Arbitrary a, Typeable a, Typeable b, Typeable c, Ord c) =>
             (a -> b -> c) -> Sig
observer2 f = observerSig (Observer (f <$> arbitrary))

observer3 :: (Arbitrary a, Arbitrary b,
              Typeable a, Typeable b, Typeable c, Typeable d,
              Ord d) =>
             (a -> b -> c -> d) -> Sig
observer3 f = observerSig (Observer (f <$> arbitrary <*> arbitrary))

observer4 :: (Arbitrary a, Arbitrary b, Arbitrary c,
              Typeable a, Typeable b, Typeable c, Typeable d, Typeable e,
              Ord e) =>
             (a -> b -> c -> d -> e) -> Sig
observer4 f = observerSig (Observer (f <$> arbitrary <*> arbitrary <*> arbitrary))
