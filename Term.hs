{-# LANGUAGE Rank2Types, ExistentialQuantification, DeriveFunctor #-}
module Term where

import Typeable
import Test.QuickCheck
import Typed
import Data.Function
import Data.Ord
import Data.List
import Data.Char
import Utils

data Named a = Named {
  index :: Int,
  name :: String,
  silent :: Bool,
  typ_ :: TypeRep,
  the :: a
  } deriving Functor

instance Show (Named a) where
  show = name

instance Eq (Named a) where
  (==) = (==) `on` index

instance Ord (Named a) where
  compare = comparing index

type Name = Named ()

erase :: Named a -> Name
erase (Named index name silent typ_ _) = Named index name silent typ_ ()

data Term a =
    Var (Var a)
  | Const (Const a)
  | forall b. App (Term (b -> a)) (Term b)

infixl 5 `App`

termEq :: Term a -> Term b -> Bool
Var x `termEq` Var y = index x == index y
Const x `termEq` Const y = index x == index y
App f x `termEq` App g y = f `termEq` g && x `termEq` y
_ `termEq` _ = False

instance Eq (Term a) where
  (==) = termEq

type Var a = Named (Gen a)
type Const a = Named (Value a)

data Value a = Undefined | Value a

value Undefined = undefined
value (Value x) = x

isUndefined :: Term a -> Bool
isUndefined (Const Named { the = Undefined }) = True
isUndefined _ = False

instance Ord (Term a) where
  compare = compareTerms

compareTerms :: Term a -> Term b -> Ordering
s `compareTerms` t = (stamp s `compare` stamp t) `orElse` (s `compareBody` t)
  where
    stamp t = (depth t, size t, -occur t)
    
    occur t = length (usort (vars t))
    
    top (Var s)   = Just (Left s)
    top (Const s) = Just (Right s)
    top _         = Nothing
    
    compareBody :: Term a -> Term b -> Ordering
    Var x `compareBody` Var y = compare (index x) (index y)
    Var x `compareBody` _ = LT
    Const x `compareBody` Var y = GT
    Const x `compareBody` Const y = compare (index x) (index y)
    Const x `compareBody` _ = LT
    App f x `compareBody` App g y =
      (f `compareTerms` g) `orElse` (x `compareTerms` y)

instance Show (Term a) where
  showsPrec p t = showString (showTerm p t)
   where
     brack s = "(" ++ s ++ ")"
     parenFun p s | p < 2 = s
                  | otherwise = brack s
     parenOp p s | p < 1 = s
                 | otherwise = brack s

     showTerm :: Int -> Term b -> String
     showTerm p (Var v) = show v
     showTerm p (Const x) = showOp (name x)
     showTerm p (Const op `App` x) | isOp (name op) = 
       brack (showTerm 1 x ++ show op)
     showTerm p (Const op `App` x `App` y) | isOp (name op) =
       parenOp p (showTerm 1 x ++ show op ++ showTerm 1 y)
     
     showTerm p (f `App` x) =
       parenFun p (showTerm 1 f ++ " " ++ showTerm 2 x)

showOp :: String -> String
showOp op | isOp op = "(" ++ op ++ ")"
          | otherwise = op

-- Generate a random variable valuation
valuation :: Gen (Var a -> a)
valuation = promote (\x -> index x `variant'` the x)
  where -- work around the fact that split doesn't work
        variant' 0 = variant 0
        variant' n = variant (-1) . variant' (n-1)

eval :: (forall a. Var a -> a) -> Term a -> a
eval env (Var x) = env x
eval env (Const x) = value (the x)
eval env (App f x) = eval env f (eval env x)

indices :: Term a -> [Int]
indices t = indices' t []
  where indices' :: Term a -> [Int] -> [Int]
        indices' (Var x) = (index x:)
        indices' (Const x) = (index x:)
        indices' (App f x) = indices' f . indices' x

depth, size :: Term a -> Int
depth (App f x) = depth f `max` (1 + depth x)
depth _ = 1
size (App f x) = size f + size x
size (Var _) = 0
size (Const _) = 1

holes :: Term a -> [(Name, Int)]
holes t = holes' 0 t []
  where holes' :: Int -> Term a -> [(Name, Int)] -> [(Name, Int)]
        holes' d (Var x) = ((erase x, d):)
        holes' d Const{} = id
        holes' d (App f x) = holes' d f . holes' (d+1) x

arrow :: TypeRep -> Maybe (TypeRep, TypeRep)
arrow ty =
  case splitTyConApp ty of
    (c, [lhs, rhs]) | c == arr -> Just (lhs, rhs)
    _ -> Nothing
  where (arr, _) = splitTyConApp (typeOf (undefined :: Int -> Int))

isArrow :: TypeRep -> Bool
isArrow ty = arrow ty /= Nothing

closure :: TypeRep -> [TypeRep]
closure ty =
  ty:
  case arrow ty of
    Nothing -> []
    Just (a, b) -> closure b

funs :: Term a -> [Name]
funs t = aux t []
  where aux :: Term b -> [Name] -> [Name]
        aux (Const x) = (erase x:)
        aux Var{} = id
        aux (App f x) = aux f . aux x

vars :: Term a -> [Name]
vars t = aux t []
  where aux :: Term b -> [Name] -> [Name]
        aux (Var x) = (erase x:)
        aux (App f x) = aux f . aux x
        aux Const{} = id

isOp :: String -> Bool
isOp "[]" = False
isOp xs = not (all isIdent xs)
  where isIdent x = isAlphaNum x || x == '\''

arity :: TypeRep -> Int
arity ty =
  case arrow ty of
    Nothing -> 0
    Just (_, rhs) -> 1 + arity rhs

