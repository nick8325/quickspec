{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators, PolyKinds #-}
module Main where
import Prelude hiding (sequence)
import Data.Typeable
import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe
import GHC.Generics
import GenericStuff
import QuickSpec hiding (Observe, observe)
import qualified QuickSpec as QS

deriving instance Typeable Observe
deriving instance Typeable Typeable

data Expr a b = Cex a
              | Vex b
              | Bex (a -> a -> a) (Expr a b) (Expr a b)
              deriving (Typeable, Generic)

instance (Arbitrary a, Typeable a, Arbitrary b, CoArbitrary b, Typeable b) =>
         Arbitrary (Expr b a) where
        arbitrary = genericArbitrary
 
instance (CoArbitrary a, Arbitrary b, CoArbitrary b) =>
         CoArbitrary (Expr b a) where
        coarbitrary = genericCoarbitrary
 
instance (Arbitrary b, Observe a, Observe b) =>
         Observe (Expr b a) where
        observe = genericObserve
 
data Program a b = Done
                 | Const a (Program a b)
                 | Load b (Program a b)
                 | Apply (a -> a -> a) (Program a b)
                 deriving (Typeable, Generic)
 
instance (Arbitrary a, Typeable a, Arbitrary b, CoArbitrary b, Typeable b) =>
         Arbitrary (Program b a) where
        arbitrary = fmap compile arbitrary
 
instance (CoArbitrary a, Arbitrary b, CoArbitrary b) =>
         CoArbitrary (Program b a) where
        coarbitrary = genericCoarbitrary
 
instance (Observe a, Arbitrary b, Observe b) =>
         Observe (Program b a) where
        observe = genericObserve

exec :: (v -> c) -> Program c v -> [c] -> [c]
exec env Done stack = stack
exec env (Const c p) stack = exec env p (c:stack)
exec env (Load v p) stack = exec env p (env v:stack)
exec env (Apply b p) (x:y:stack) = exec env p (b x y:stack)
 
value :: (v -> c) -> Expr c v -> c
value env (Cex c) = c
value env (Vex v) = env v
value env (Bex b e1 e2) = b (value env e1) (value env e2)

sequence :: Program v c -> Program v c -> Program v c
sequence Done p = p
sequence (Const c p) p' = Const c (sequence p p')
sequence (Load v p) p' = Load v (sequence p p')
sequence (Apply b p) p' = Apply b (sequence p p')

compile :: Expr v c -> Program v c
compile (Cex c) = Const c Done
compile (Vex v) = Load v Done
compile (Bex b e1 e2) = sequence (compile e2) (sequence (compile e1) (Apply b Done))

main =
  quickSpec signature {
    instances = [
        makeInstance (\(Dict :: Dict (Observe A)) -> QS.Observe Dict (observe :: A -> Gen Observation)),
        inst5 (Sub Dict :: (Arbitrary A, Typeable A, Arbitrary B, CoArbitrary B, Typeable B) :- Arbitrary (Expr B A)),
        inst5 (Sub Dict :: (Arbitrary A, Typeable A, Arbitrary B, CoArbitrary B, Typeable B) :- Arbitrary (Program B A)),
        inst3 (Sub Dict :: (CoArbitrary A, Arbitrary B, CoArbitrary B) :- CoArbitrary (Expr B A)),
        inst3 (Sub Dict :: (CoArbitrary A, Arbitrary B, CoArbitrary B) :- CoArbitrary (Program B A)),
        inst3 (Sub Dict :: (Arbitrary B, Observe A, Observe B) :- Observe (Expr B A)),
        inst3 (Sub Dict :: (Arbitrary B, Observe A, Observe B) :- Observe (Program B A)),
        inst (Sub Dict :: () :- Typeable Int),
        inst (Sub Dict :: () :- Observe Int) ],
    constants = [
      constant ":" ((:) :: A -> [A] -> [A]),
      constant "[]" ([] :: [A]),
      constant "compile" (compile :: Expr A B -> Program A B),
      constant "sequence" (sequence :: Program A B -> Program A B -> Program A B),
      constant "value" (value :: (A -> B) -> Expr B A -> B),
      constant "exec" (exec :: (A -> B) -> Program B A -> [B] -> [B]) ]}
