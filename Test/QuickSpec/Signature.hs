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
import Control.Monad

class Signature a where
  signature :: a -> Sig

instance Signature Sig where
  signature = id

instance Signature a => Signature [a] where
  signature = mconcat . map signature

data Sig = Sig {
  -- Constants, variables and observation functions.
  constants :: TypeRel Constant,
  variables :: TypeRel Variable,
  observers :: TypeMap Observer,

  -- Ord instances, added whenever the 'fun' family of functions is used.
  ords :: TypeMap Observer,

  -- Witnesses for Typeable. The following types must have witnesses:
  -- * Any function argument.
  -- * Any function result.
  -- * Any partially-applied function type.
  -- * Any variable type.
  witnesses :: TypeMap Witnessed,

  -- Depth of terms in the universe.
  maxDepth_ :: First Int
  }

maxDepth :: Sig -> Int
maxDepth = fromMaybe 3 . getFirst . maxDepth_

updateDepth :: Int -> Sig -> Sig
updateDepth n sig = sig { maxDepth_ = First (Just n) }

instance Show Sig where show = unlines . summarise

summarise :: Sig -> [String]
summarise sig =
  [ "-- functions --" ] ++
    describe showOp (sym . unConstant) (not . isSilent) constants ++
  concat [
    [ "", "-- background functions --" ] ++
      describe showOp (sym . unConstant) isSilent constants
    | not (null (filter (some isSilent) (TypeRel.toList (constants sig)))) ] ++
  [ "", "-- variables --" ] ++
    describe id (sym . unVariable) (const True) variables ++
  warn [ "", "-- the following types are using non-standard equality --" ]
    (Map.keys (observers sig)) ++

  warn ["",
        "-- WARNING: the following types are uninhabited --"]
    [ typeOf w
    | Some k <- TypeRel.toList (constants sig),
      ty@(Some (Witness w)) <- constantArgs sig k,
      ty `notElem` saturatedTypes sig,
      null (TypeRel.lookup w (variables sig)) ] ++
  warn ["",
        "-- WARNING: there are no variables of the following types; consider adding some --"]
    [ typeOf w
    | Some k <- TypeRel.toList (constants sig),
      ty@(Some (Witness w)) <- constantArgs sig k,
      -- There is a non-variable term of this type and it appears as the
      -- argument to some function
      null (TypeRel.lookup w (variables sig)) ] ++
  warn ["",
        "-- WARNING: cannot test the following types; ",
        "            consider using 'fun' instead of 'blind' or using 'observe' --"]
    [ typeOf w
    | Some (Witness w) <- saturatedTypes sig,
      -- The type is untestable and is the result type of a constant
      not (testable sig w) ]

  where
    describe :: (String -> String) -> (forall a. f a -> Symbol) ->
                (forall a. f a -> Bool) ->
                (Sig -> TypeRel f) -> [String]
    describe decorate un p f =
      [ intercalate ", " (map (decorate . name) xs) ++ " :: " ++ show (symbolType x)
      | xs@(x:_) <- partitionBy symbolType (map (some un) (filter (some p) (TypeRel.toList (f sig)))) ]

    warn _ [] = []
    warn msg xs = msg ++ map show (usort xs)

    isSilent (Constant (Atom { sym = sym })) = silent sym

data Observer a = forall b. Ord b => Observer (Gen (a -> b))

observe x sig =
  TypeMap.lookup (TypeMap.lookup (error msg) x (ords sig))
               x (observers sig)
  where msg = "Test.QuickSpec.Signature.observe: no observers found for type " ++ show (typeOf x)

emptySig :: Sig
emptySig = Sig TypeRel.empty TypeRel.empty TypeMap.empty TypeMap.empty TypeMap.empty mempty

instance Monoid Sig where
  mempty = emptySig
  s1 `mappend` s2 =
    Sig {
      constants = renumber (mapConstant . alter) 0 constants',
      variables = renumber (mapVariable . alter) (length constants') variables',
      observers = observers s1 `mappend` observers s2,
      ords = ords s1 `mappend` ords s2,
      witnesses = witnesses s1 `mappend` witnesses s2,
      maxDepth_ = maxDepth_ s1 `mappend` maxDepth_ s2 }
    where constants' = TypeRel.toList (constants s1) ++
                       TypeRel.toList (constants s2)
          -- Overwrite variables if they're declared twice!
          variables' = TypeRel.toList (variables s1 `mappend` variables s2)

          renumber :: (forall a. Int -> f a -> f a) ->
                      Int -> [Some f] -> TypeRel f
          renumber alter n =
            TypeRel.fromList .
            zipWith (\x -> mapSome (alter x)) [n..]

          alter :: Int -> Symbol -> Symbol
          alter n x = x { index = n }

constantSig :: Typeable a => Constant a -> Sig
constantSig x = emptySig { constants = TypeRel.singleton x }

variableSig :: forall a. Typeable a => [Variable a] -> Sig
variableSig x = emptySig { variables = TypeRel.fromList (map Some x) }

observerSig :: forall a. Typeable a => Observer a -> Sig
observerSig x = emptySig { observers = TypeMap.singleton x }

typeSig :: Typeable a => a -> Sig
typeSig x = emptySig { witnesses = TypeMap.singleton (Witness x) }

ordSig :: Typeable a => Observer a -> Sig
ordSig x = emptySig { ords = TypeMap.singleton x }

withDepth :: Int -> Sig
withDepth n = updateDepth n emptySig

undefinedSig :: forall a. Typeable a => String -> a -> Sig
undefinedSig x u = constantSig (Constant (Atom ((symbol x 0 u) { undef = True }) u))

primCon0 :: forall a. Typeable a => Int -> String -> a -> Sig
primCon0 n x f = constantSig (Constant (Atom (symbol x n f) f))
                 `mappend` typeSig (undefined :: a)

primCon1 :: forall a b. (Typeable a, Typeable b) =>
          Int -> String -> (a -> b) -> Sig
primCon1 n x f = primCon0 n x f
                 `mappend` typeSig (undefined :: a)
                 `mappend` typeSig (undefined :: b)

primCon2 :: forall a b c. (Typeable a, Typeable b, Typeable c) =>
          Int -> String -> (a -> b -> c) -> Sig
primCon2 n x f = primCon1 n x f
                 `mappend` typeSig (undefined :: b)
                 `mappend` typeSig (undefined :: c)

primCon3 :: forall a b c d. (Typeable a, Typeable b, Typeable c, Typeable d) =>
          Int -> String -> (a -> b -> c -> d) -> Sig
primCon3 n x f = primCon2 n x f
                 `mappend` typeSig (undefined :: c)
                 `mappend` typeSig (undefined :: d)

primCon4 :: forall a b c d e. (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e) =>
          Int -> String -> (a -> b -> c -> d -> e) -> Sig
primCon4 n x f = primCon3 n x f
                 `mappend` typeSig (undefined :: d)
                 `mappend` typeSig (undefined :: e)

blind0 :: forall a. Typeable a => String -> a -> Sig
blind0 = primCon0 0
blind1 :: forall a b. (Typeable a, Typeable b) =>
          String -> (a -> b) -> Sig
blind1 = primCon1 1
blind2 :: forall a b c. (Typeable a, Typeable b, Typeable c) =>
          String -> (a -> b -> c) -> Sig
blind2 = primCon2 2
blind3 :: forall a b c d. (Typeable a, Typeable b, Typeable c, Typeable d) =>
          String -> (a -> b -> c -> d) -> Sig
blind3 = primCon3 3
blind4 :: forall a b c d e. (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e) =>
          String -> (a -> b -> c -> d -> e) -> Sig
blind4 = primCon4 4

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

vars :: forall a. (Arbitrary a, Typeable a) => [String] -> a -> Sig
vars xs v = variableSig [ Variable (Atom (symbol x 0 v) (arbitrary `asTypeOf` return v)) | x <- xs ]
            `mappend` typeSig (undefined :: a)

con, fun0 :: (Ord a, Typeable a) => String -> a -> Sig
con = fun0
fun0 x f = blind0 x f
           `mappend` ord f

fun1 :: (Typeable a,
         Typeable b, Ord b) =>
        String -> (a -> b) -> Sig
fun1 x f = blind1 x f
           `mappend` ord (f undefined)

fun2 :: (Typeable a, Typeable b,
         Typeable c, Ord c) =>
        String -> (a -> b -> c) -> Sig
fun2 x f = blind2 x f
           `mappend` ord (f undefined undefined)

fun3 :: (Typeable a, Typeable b, Typeable c,
         Typeable d, Ord d) =>
        String -> (a -> b -> c -> d) -> Sig
fun3 x f = blind3 x f
           `mappend` ord (f undefined undefined undefined)

fun4 :: (Typeable a, Typeable b, Typeable c, Typeable d,
         Typeable e, Ord e) =>
        String -> (a -> b -> c -> d -> e) -> Sig
fun4 x f = blind4 x f
           `mappend` ord (f undefined undefined undefined undefined)

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

testable :: Typeable a => Sig -> a -> Bool
testable sig x =
  typeOf x `Map.member` observers sig ||
  typeOf x `Map.member` ords sig

-- Given a constant, find the types of its partial applications.
constantApplications :: forall a. Typeable a => Sig -> Constant a -> [Witness]
constantApplications sig (Constant (Atom {sym = sym })) =
  map (findWitness sig)
    (take (symbolArity sym + 1)
     (iterate rightArrow (typeOf (undefined :: a))))

-- Find the argument types of a constant.
constantArgs :: forall a. Typeable a => Sig -> Constant a -> [Witness]
constantArgs sig (Constant (Atom { sym = sym })) =
  map (findWitness sig)
    (take (symbolArity sym)
     (unfoldr splitArrow (typeOf (undefined :: a))))

-- Find the type of a saturated constant.
constantRes :: forall a. Typeable a => Sig -> Constant a -> Witness
constantRes sig (Constant (Atom { sym = sym })) =
  findWitness sig
    (iterate (snd . fromMaybe (error msg) . splitArrow)
       (typeOf (undefined :: a)) !! symbolArity sym)
  where msg = "Test.QuickSpec.Signature.constantRes: type oversaturated"

-- The set of types returned by saturated constants.
saturatedTypes :: Sig -> [Witness]
saturatedTypes sig =
  usort $
    [ constantRes sig k
    | Some k <- TypeRel.toList (constants sig) ]

-- Given a type, find a witness that it's a function.
witnessArrow :: Typeable a => Sig -> a -> Maybe (Witness, Witness)
witnessArrow sig x = do
  (lhs, rhs) <- splitArrow (typeOf x)
  liftM2 (,) (lookupWitness sig lhs) (lookupWitness sig rhs)

-- lhsWitnesses sig x is the set of witnessed function types that
-- might accept x as a parameter. There is no guarantee that
-- any particular type is inhabited.
lhsWitnesses :: Typeable a => Sig -> a -> [Witness]
lhsWitnesses sig x =
  [ lhs
  | Some (Witness w) <- TypeMap.toList (witnesses sig),
    Just (lhs, rhs) <- [witnessArrow sig w],
    witnessType rhs == typeOf x ]

findWitness :: Sig -> TypeRep -> Witness
findWitness sig ty =
  fromMaybe (error "Test.QuickSpec.Signature.findWitness: missing type")
    (lookupWitness sig ty)

lookupWitness :: Sig -> TypeRep -> Maybe Witness
lookupWitness sig ty = Map.lookup ty (witnesses sig)
