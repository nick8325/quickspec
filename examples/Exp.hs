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
 
data Instruction a b =
    Const a
  | Load b
  | Apply (a -> a -> a)
  deriving (Typeable, Generic)
 
instance (Arbitrary a, Typeable a, Arbitrary b, CoArbitrary b, Typeable b) =>
         Arbitrary (Instruction b a) where
        arbitrary =
          oneof [fmap Const arbitrary, fmap Load arbitrary, fmap Apply arbitrary]
 
instance (CoArbitrary a, Arbitrary b, CoArbitrary b) =>
         CoArbitrary (Instruction b a) where
        coarbitrary = genericCoarbitrary
 
instance (Observe a, Arbitrary b, Observe b) =>
         Observe (Instruction b a) where
        observe = genericObserve

exec :: (v -> c) -> [Instruction c v] -> [c] -> Maybe [c]
exec env [] stack = Just stack
exec env (Const c:p) stack = exec env p (c:stack)
exec env (Load v:p) stack = exec env p (env v:stack)
exec env (Apply b:p) (x:y:stack) = exec env p (b x y:stack)
exec _ _ _ = Nothing
 
value :: (v -> c) -> Expr c v -> c
value env (Cex c) = c
value env (Vex v) = env v
value env (Bex b e1 e2) = b (value env e1) (value env e2)

compile :: Expr v c -> [Instruction v c]
compile (Cex c) = [Const c]
compile (Vex v) = [Load v]
compile (Bex b e1 e2) = compile e2 ++ compile e1 ++ [Apply b]

bg =
  signature {
    constants = [
      constant ":" ((:) :: A -> [A] -> [A]),
      constant "[]" ([] :: [A]),
      constant "Just" (Just :: A -> Maybe A),
      constant "++" ((++) :: [A] -> [A] -> [A]) ]}

main =
  quickSpecWithBackground bg signature {
    instances = [
        names (NamesFor ["i"] :: NamesFor (Instruction A B)),
        names (NamesFor ["e"] :: NamesFor (Expr A B)),
        names (NamesFor ["env"] :: NamesFor (A -> B)),
        makeInstance (\(Dict :: Dict (Observe A)) -> QS.Observe Dict (observe :: A -> Gen Observation)),
        inst5 (Sub Dict :: (Arbitrary A, Typeable A, Arbitrary B, CoArbitrary B, Typeable B) :- Arbitrary (Expr B A)),
        inst5 (Sub Dict :: (Arbitrary A, Typeable A, Arbitrary B, CoArbitrary B, Typeable B) :- Arbitrary (Instruction B A)),
        inst3 (Sub Dict :: (CoArbitrary A, Arbitrary B, CoArbitrary B) :- CoArbitrary (Expr B A)),
        inst3 (Sub Dict :: (CoArbitrary A, Arbitrary B, CoArbitrary B) :- CoArbitrary (Instruction B A)),
        inst3 (Sub Dict :: (Arbitrary B, Observe A, Observe B) :- Observe (Expr B A)),
        inst3 (Sub Dict :: (Arbitrary B, Observe A, Observe B) :- Observe (Instruction B A)),
        inst (Sub Dict :: () :- Typeable Int),
        inst (Sub Dict :: () :- Observe Int) ],
    constants = [
      constant "compile" (compile :: Expr A B -> [Instruction A B]),
      constant "value" (value :: (A -> B) -> Expr B A -> B),
      constant "exec" (exec :: (A -> B) -> [Instruction B A] -> [B] -> Maybe [B]) ]}
