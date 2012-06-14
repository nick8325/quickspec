{-# LANGUAGE ExistentialQuantification, StandaloneDeriving, DeriveDataTypeable #-}
module Signature where

import Control.Applicative hiding (some)
import Typeable
import Data.Monoid
import Test.QuickCheck
import Term
import Typed
import Data.List
import qualified Data.Map as Map
import Utils
import Data.Maybe

deriving instance Typeable1 Gen

class Signature a where
  signature :: a -> Sig

instance Signature Sig where
  signature = id

instance Signature a => Signature [a] where
  signature = mconcat . map signature

data Sig = Sig {
  constants :: TypeMap (C [] (C Named Value)),
  variables :: TypeMap (C [] (C Named Gen)),
  observers :: TypeMap Observer,
  ords :: TypeMap Observer,
  witnesses :: TypeMap (K ()),
  maxDepth_ :: First Int
  }

maxDepth :: Sig -> Int
maxDepth = fromMaybe 3 . getFirst . maxDepth_

names :: TypeMap (C [] (C Named f)) -> [Name]
names = concatMap (some (map (erase . unC) . unC)) . Map.elems

types :: Sig -> [TypeRep]
types sig = usort (map typ_ (names (constants sig)) ++ map typ_ (names (variables sig)))

instance Show Sig where show = unlines . summarise

summarise :: Sig -> [String]
summarise sig =
  [ "-- functions --" ] ++ describe showOp constants ++
  [ "", "-- variables --" ] ++ describe id variables ++
  concat
  [ [ "", "** the following types are using non-standard equality **" ] ++
    map show (Map.keys (observers sig))
  | not (Map.null (observers sig)) ] ++
  concat
  [ [""] ++
    starry [" WARNING: CANNOT NOT TEST THE FOLLOWING TYPES ",
            "   (add an Ord instance or use 'observe')     "] ++
    [""] ++
    map show untestable
  | not (null untestable) ]
    
  where
    describe decorate f =
      [ intercalate ", " (map (decorate . name) xs) ++ " :: " ++ show (typ_ x) 
      | xs@(x:_) <- partitionBy typ_ (names (f sig)) ]
    starry xss@(xs:_) = map horizStars $ [stars] ++ xss ++ [stars]
      where stars = replicate (length xs) '*'
            horizStars xs = "****" ++ xs ++ "****"
    untestable = filter isTerminal (filter (not . flip testable sig) (inhabitedTypes sig))
    isTerminal ty =
      case arrow ty of
        Nothing -> True
        Just (_, rhs) -> not (rhs `elem` inhabitedTypes sig)

data Observer a = forall b. Ord b => Observer (Gen (a -> b)) deriving Typeable

emptySig :: Sig
emptySig = Sig Typed.empty Typed.empty Typed.empty Typed.empty Typed.empty mempty

instance Monoid Sig where
  mempty = emptySig
  s1 `mappend` s2 =
    Sig {
      constants = renumber 0 constants',
      variables = renumber (length constants') variables',
      observers = observers s1 `mappend` observers s2,
      ords = ords s1 `mappend` ords s2,
      witnesses = witnesses s1 `mappend` witnesses s2, 
      maxDepth_ = maxDepth_ s1 `mappend` maxDepth_ s2 }
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

witness :: Typeable a => a -> Sig
witness x = emptySig { witnesses = Typed.fromList [Some (witnessing x)] }
  where witnessing :: a -> K () a
        witnessing x = K ()

ordSig :: Typeable a => Observer a -> Sig
ordSig x = emptySig { ords = Typed.fromList [Some x] }

withDepth :: Int -> Sig
withDepth n = emptySig { maxDepth_ = First (Just n) }

constantValue :: Typeable a => String -> Value a -> Sig
constantValue x v = constantSig (Named 0 x False (typeOf (unValue v)) v) `mappend` witness (unValue v)
  where unValue (Value x) = x

blind0 :: Typeable a => String -> a -> Sig
blind0 x f = constantValue x (Value f)

blind1 :: (Typeable a, Typeable b) => String -> (a -> b) -> Sig
blind1 x f = blind0 x f `mappend` witness (f undefined)

blind2 :: (Typeable a, Typeable b, Typeable c) => String -> (a -> b -> c) -> Sig
blind2 x f = blind1 x f `mappend` witness (f undefined undefined)

blind3 :: (Typeable a, Typeable b, Typeable c, Typeable d) => String -> (a -> b -> c -> d) -> Sig
blind3 x f = blind1 x f `mappend` witness (f undefined undefined undefined)

blind4 :: (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e) => String -> (a -> b -> c -> d -> e) -> Sig
blind4 x f = blind1 x f `mappend` witness (f undefined undefined undefined undefined)

ord :: (Ord a, Typeable a) => a -> Sig
ord x = ordSig (Observer (return id) `observing` x)

observing :: Observer a -> a -> Observer a
observing x _ = x

silence :: Signature a => a -> Sig
silence sig =
  sig' { constants = mapValues (C . map (C . silence1 . unC) . unC) (constants sig'),
         variables = mapValues (C . map (C . silence1 . unC) . unC) (variables sig') }
  where sig' = signature sig
        silence1 x = x { silent = True }

vars :: (Arbitrary a, Typeable a) => [String] -> a -> Sig
vars xs v = mconcat [ var x v | x <- xs ]

var :: (Arbitrary a, Typeable a) => String -> a -> Sig
var x v = variableSig (Named 0 x False (typeOf v) (arbitrary `asTypeOf` return v))

con, fun0 :: (Ord a, Typeable a) => String -> a -> Sig
con = fun0
fun0 x f = blind0 x f `mappend` ord f

fun1 :: (Typeable a,
         Typeable b, Ord b) =>
        String -> (a -> b) -> Sig
fun1 x f = blind1 x f `mappend` ord (f undefined)

fun2 :: (Typeable a, Typeable b,
         Typeable c, Ord c) =>
        String -> (a -> b -> c) -> Sig
fun2 x f = blind2 x f `mappend`
           ord (f undefined undefined)

fun3 :: (Typeable a, Typeable b, Typeable c,
         Typeable d, Ord d) =>
        String -> (a -> b -> c -> d) -> Sig
fun3 x f = blind3 x f `mappend`
           ord (f undefined undefined undefined)

fun4 :: (Typeable a, Typeable b, Typeable c, Typeable d,
         Typeable e, Ord e) =>
        String -> (a -> b -> c -> d -> e) -> Sig
fun4 x f = blind4 x f `mappend`
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

inhabitedTypes :: Sig -> [TypeRep]
inhabitedTypes = usort . map (some (typeOf . witness)) . toList . witnesses
  where witness :: K () a -> a
        witness = undefined

testableTypes :: Sig -> [TypeRep]
testableTypes sig = filter (flip testable sig) . inhabitedTypes $ sig

testable :: TypeRep -> Sig -> Bool
testable ty sig =
  ty `Map.member` observers sig ||
  ty `Map.member` ords sig

argTypes sig ty =
  [ ty1 | (ty1, ty2) <- catMaybes (map arrow (inhabitedTypes sig)), ty2 == ty ]

