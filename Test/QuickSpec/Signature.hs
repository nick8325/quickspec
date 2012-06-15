{-# LANGUAGE Rank2Types, ExistentialQuantification, ScopedTypeVariables #-}
module Test.QuickSpec.Signature where

import Control.Applicative hiding (some)
import Test.QuickSpec.Utils.Typeable
import Data.Monoid
import Test.QuickCheck
import Test.QuickSpec.Term hiding (var)
import Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import Test.QuickSpec.Utils.TypeMap(TypeMap)
import qualified Test.QuickSpec.Utils.TypeRel as TypeRel
import Test.QuickSpec.Utils.TypeRel(TypeRel)
import Data.List
import qualified Data.Map as Map
import Test.QuickSpec.Utils
import Data.Maybe

class Signature a where
  signature :: a -> Sig

instance Signature Sig where
  signature = id

instance Signature a => Signature [a] where
  signature = mconcat . map signature

data Sig = Sig {
  constants :: TypeRel Constant,
  variables :: TypeRel Variable,
  observers :: TypeMap Observer,
  ords :: TypeMap Observer,
  types :: TypeMap Witnessed,
  cotypes :: TypeMap Witnessed,
  maxDepth_ :: First Int
  }

maxDepth :: Sig -> Int
maxDepth = fromMaybe 3 . getFirst . maxDepth_

updateDepth :: Int -> Sig -> Sig
updateDepth n sig = sig { maxDepth_ = First (Just n) }

instance Show Sig where show = unlines . summarise

summarise :: Sig -> [String]
summarise sig =
  [ "-- functions --" ] ++ describe showOp (sym . unConstant) constants ++
  [ "", "-- variables --" ] ++ describe id (sym . unVariable) variables ++
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
    describe :: (String -> String) -> (forall a. f a -> Symbol) ->
                (Sig -> TypeRel f) -> [String]
    describe decorate un f =
      [ intercalate ", " (map (decorate . name) xs) ++ " :: " ++ show (symbolType x)
      | xs@(x:_) <- partitionBy symbolType (map (some un) (TypeRel.toList (f sig))) ]
    starry xss@(xs:_) = map horizStars $ [stars] ++ xss ++ [stars]
      where stars = replicate (length xs) '*'
            horizStars xs = "****" ++ xs ++ "****"
    untestable = filter isTerminal (filter (not . flip testable sig) (inhabitedTypes sig))
    isTerminal ty =
      case arrow ty of
        Nothing -> True
        Just (_, rhs) -> not (rhs `elem` inhabitedTypes sig)

data Observer a = forall b. Ord b => Observer (Gen (a -> b))

observe x sig =
  TypeMap.lookup (TypeMap.lookup (error msg) x (ords sig))
               x (observers sig)
  where msg = "Signature.observe: no observers found for type " ++ show (typeOf x)

emptySig :: Sig
emptySig = Sig TypeRel.empty TypeRel.empty TypeMap.empty TypeMap.empty TypeMap.empty TypeMap.empty mempty

instance Monoid Sig where
  mempty = emptySig
  s1 `mappend` s2 =
    Sig {
      constants = renumber (mapConstant . alter) 0 constants',
      variables = renumber (mapVariable . alter) (length constants') variables',
      observers = observers s1 `mappend` observers s2,
      ords = ords s1 `mappend` ords s2,
      types = types s1 `mappend` types s2,
      cotypes = cotypes s1 `mappend` cotypes s2,
      maxDepth_ = maxDepth_ s1 `mappend` maxDepth_ s2 }
    where constants' = TypeRel.toList (constants s1) ++
                       TypeRel.toList (constants s2)
          variables' = TypeRel.toList (variables s1) ++
                       TypeRel.toList (variables s2)

          renumber :: (forall a. Int -> f a -> f a) ->
                      Int -> [Some f] -> TypeRel f
          renumber alter n =
            TypeRel.fromList .
            zipWith (\x -> mapSome (alter x)) [n..]

          alter :: Int -> Symbol -> Symbol
          alter n x = x { index = n }

constantSig :: forall a. Typeable a => Constant a -> Sig
constantSig x = emptySig { constants = TypeRel.singleton x }
                `mappend` typeSig (undefined :: a)

variableSig :: forall a. Typeable a => Variable a -> Sig
variableSig x = emptySig { variables = TypeRel.singleton x }
                `mappend` cotypeSig (undefined :: a)

observerSig :: Typeable a => Observer a -> Sig
observerSig x = emptySig { observers = TypeMap.singleton x }

typeSig :: Typeable a => a -> Sig
typeSig x = emptySig { types = TypeMap.singleton (Witnessed x) }

cotypeSig :: Typeable a => a -> Sig
cotypeSig x = emptySig { cotypes = TypeMap.singleton (Witnessed x) }

ordSig :: Typeable a => Observer a -> Sig
ordSig x = emptySig { ords = TypeMap.singleton x }

withDepth :: Int -> Sig
withDepth n = updateDepth n emptySig

undefinedSig :: forall a. Typeable a => String -> a -> Sig
undefinedSig x u = constantSig (Constant (Atom ((symbol x u) { undef = True }) u))

blind0 :: forall a. Typeable a => String -> a -> Sig
blind0 x f = constantSig (Constant (Atom (symbol x f) f))

blind1 :: forall a b. (Typeable a, Typeable b) =>
          String -> (a -> b) -> Sig
blind1 x f = blind0 x f `mappend` cotypeSig (undefined :: a)
                        `mappend` typeSig (undefined :: b)

blind2 :: forall a b c. (Typeable a, Typeable b, Typeable c) =>
          String -> (a -> b -> c) -> Sig
blind2 x f = blind1 x f `mappend` cotypeSig (undefined :: a)
                        `mappend` cotypeSig (undefined :: b)
                        `mappend` typeSig (undefined :: c)

blind3 :: forall a b c d. (Typeable a, Typeable b, Typeable c, Typeable d) =>
          String -> (a -> b -> c -> d) -> Sig
blind3 x f = blind1 x f `mappend` cotypeSig (undefined :: a)
                        `mappend` cotypeSig (undefined :: b)
                        `mappend` cotypeSig (undefined :: c)
                        `mappend` typeSig (undefined :: d)

blind4 :: forall a b c d e. (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e) =>
          String -> (a -> b -> c -> d -> e) -> Sig
blind4 x f = blind1 x f `mappend` cotypeSig (undefined :: a)
                        `mappend` cotypeSig (undefined :: b)
                        `mappend` cotypeSig (undefined :: c)
                        `mappend` cotypeSig (undefined :: d)
                        `mappend` typeSig (undefined :: e)

ord :: (Ord a, Typeable a) => a -> Sig
ord x = ordSig (Observer (return id) `observing` x)

observing :: Observer a -> a -> Observer a
observing x _ = x

silence :: Signature a => a -> Sig
silence sig =
  sig' { constants = TypeRel.mapValues (mapConstant silence1) (constants sig'),
         variables = TypeRel.mapValues (mapVariable silence1) (variables sig') }
  where sig' = signature sig
        silence1 x = x { silent = True }

vars :: (Arbitrary a, Typeable a) => [String] -> a -> Sig
vars xs v = mconcat [ var x v | x <- xs ]

var :: (Arbitrary a, Typeable a) => String -> a -> Sig
var x v = variableSig (Variable (Atom (symbol x v) (arbitrary `asTypeOf` return v)))

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

observer0 :: (Typeable a, Typeable b, Ord b) => (a -> b) -> Sig
observer0 f = observerSig (Observer (return f))

observer1 :: (Arbitrary a, Typeable a, Typeable b, Typeable c, Ord c) =>
             (a -> b -> c) -> Sig
observer1 f = observerSig (Observer (f <$> arbitrary))

observer2 :: (Arbitrary a, Arbitrary b,
              Typeable a, Typeable b, Typeable c, Typeable d,
              Ord d) =>
             (a -> b -> c -> d) -> Sig
observer2 f = observerSig (Observer (f <$> arbitrary <*> arbitrary))

observer3 :: (Arbitrary a, Arbitrary b, Arbitrary c,
              Typeable a, Typeable b, Typeable c, Typeable d, Typeable e,
              Ord e) =>
             (a -> b -> c -> d -> e) -> Sig
observer3 f = observerSig (Observer (f <$> arbitrary <*> arbitrary <*> arbitrary))

observer4 :: (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d,
              Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable f,
              Ord f) =>
             (a -> b -> c -> d -> e -> f) -> Sig
observer4 f = observerSig (Observer (f <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary))

inhabitedTypes :: Sig -> [TypeRep]
inhabitedTypes = usort . map (some (typeOf . witness)) . TypeMap.toList . types

testableTypes :: Sig -> [TypeRep]
testableTypes sig = filter (flip testable sig) . inhabitedTypes $ sig

testable :: TypeRep -> Sig -> Bool
testable ty sig =
  ty `Map.member` observers sig ||
  ty `Map.member` ords sig

arrow :: TypeRep -> Maybe (TypeRep, TypeRep)
arrow ty =
  case splitTyConApp ty of
    (c, [lhs, rhs]) | c == arr -> Just (lhs, rhs)
    _ -> Nothing
  where (arr, _) = splitTyConApp (typeOf (undefined :: Int -> Int))

findWitness :: Sig -> TypeRep -> Witness
findWitness sig ty =
  Map.findWithDefault
    (error $ "Generate.witness: type " ++ show ty ++ " not found")
    ty (types sig `mappend` cotypes sig)
