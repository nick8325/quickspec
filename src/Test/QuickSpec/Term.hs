-- | Terms and evaluation.

{-# LANGUAGE CPP, RankNTypes, ExistentialQuantification, DeriveFunctor, DeriveDataTypeable #-}
module Test.QuickSpec.Term where

#include "errors.h"
import Test.QuickSpec.Utils.Typeable
import Test.QuickCheck
import Data.Function
import Data.Ord
import Data.Char
import Test.QuickSpec.Utils

data Symbol = Symbol {
  index :: Int,
  name :: String,
  symbolArity :: Int,
  silent :: Bool,
  undef :: Bool,
  symbolType :: TypeRep }

symbol :: Typeable a => String -> Int -> a -> Symbol
symbol x arity v = Symbol 0 x arity False False (typeOf v)

instance Show Symbol where
  show = showOp . name

instance Eq Symbol where
  (==) = (==) `on` index

instance Ord Symbol where
  compare = comparing index

data Term =
    Var Symbol
  | Const Symbol
  | App Term Term deriving Eq

infixl 5 `App`

instance Ord Term where
  compare = comparing stamp
    where
      stamp t = (depth t, size t, -occur t, body t)

      occur t = length (usort (vars t))

      body (Var x) = Left (Left x)
      body (Const x) = Left (Right x)
      body (App f x) = Right (f, x)

instance Show Term where
  showsPrec p t = showString (showTerm p t)
   where
     brack s = "(" ++ s ++ ")"
     parenFun p s | p < 2 = s
                  | otherwise = brack s
     parenOp p s | p < 1 = s
                 | otherwise = brack s

     showTerm p (Var v) = show v
     showTerm p (Const x) = show x
     showTerm p (Const op `App` x) | isOp (name op) =
       brack (showTerm 1 x ++ name op)
     showTerm p (Const op `App` x `App` y) | isOp (name op) =
       parenOp p (showTerm 1 x ++ name op ++ showTerm 1 y)

     showTerm p (f `App` x) =
       parenFun p (showTerm 1 f ++ " " ++ showTerm 2 x)

showOp :: String -> String
showOp op | isOp op = "(" ++ op ++ ")"
          | otherwise = op

isOp :: String -> Bool
isOp "[]" = False
isOp xs = not (all isIdent xs)
  where isIdent x = isAlphaNum x || x == '\'' || x == '_'

isUndefined :: Term -> Bool
isUndefined (Const Symbol { undef = True }) = True
isUndefined _ = False

symbols :: Term -> [Symbol]
symbols t = symbols' t []
  where symbols' (Var x) = (x:)
        symbols' (Const x) = (x:)
        symbols' (App f x) = symbols' f . symbols' x

depth, size :: Term -> Int
depth (App f x) = depth f `max` (1 + depth x)
depth _ = 1
size (App f x) = size f + size x
size (Var _) = 0
size (Const _) = 1

holes :: Term -> [(Symbol, Int)]
holes t = holes' 0 t []
  where holes' d (Var x) = ((x, d):)
        holes' d Const{} = id
        holes' d (App f x) = holes' d f . holes' (d+1) x

functor :: Term -> Symbol
functor (Var x) = x
functor (Const x) = x
functor (App f x) = functor f

args :: Term -> [Term]
args = reverse . args'
  where args' Var{} = []
        args' Const{} = []
        args' (App f x) = x:args' f

funs :: Term -> [Symbol]
funs t = aux t []
  where aux (Const x) = (x:)
        aux Var{} = id
        aux (App f x) = aux f . aux x

vars :: Term -> [Symbol]
vars t = aux t []
  where aux (Var x) = (x:)
        aux (App f x) = aux f . aux x
        aux Const{} = id

mapVars :: (Symbol -> Symbol) -> Term -> Term
mapVars f (Var x) = Var (f x)
mapVars f (Const x) = Const x
mapVars f (App t u) = App (mapVars f t) (mapVars f u)

data Expr a = Expr {
  term :: Term,
  arity :: {-# UNPACK #-} !Int,
  eval :: (forall b. Variable b -> b) -> a }
  deriving Typeable

instance Eq (Expr a) where
  (==) = (==) `on` term

instance Ord (Expr a) where
  compare = comparing term

instance Show (Expr a) where
  show = show . term

data Atom a = Atom {
  sym :: Symbol,
  value :: a } deriving Functor

data PGen a = PGen {
  totalGen :: Gen a,
  partialGen :: Gen a
  }

pgen :: Gen a -> PGen a
pgen g = PGen g g

type Strategy = forall a. Symbol -> PGen a -> Gen a

instance Functor PGen where
  fmap f (PGen tot par) = PGen (fmap f tot) (fmap f par)

newtype Variable a = Variable { unVariable :: Atom (PGen a) } deriving Functor
newtype Constant a = Constant { unConstant :: Atom a } deriving Functor

mapVariable :: (Symbol -> Symbol) -> Variable a -> Variable a
mapVariable f (Variable v) = Variable v { sym = f (sym v) }

mapConstant :: (Symbol -> Symbol) -> Constant a -> Constant a
mapConstant f (Constant v) = Constant v { sym = f (sym v) }

-- Generate a random variable valuation
valuation :: Strategy -> Gen (Variable a -> a)
valuation strat = promote (\(Variable x) -> index (sym x) `variant'` strat (sym x) (value x))
  where -- work around the fact that split doesn't work
        variant' 0 = variant (0 :: Int)
        variant' n = variant (-1 :: Int) . variant' (n-1)

var :: Variable a -> Expr a
var v@(Variable (Atom x _)) = Expr (Var x) (symbolArity x) (\env -> env v)

con :: Constant a -> Expr a
con (Constant (Atom x v)) = Expr (Const x) (symbolArity x) (const v)

app :: Expr (a -> b) -> Expr a -> Expr b
app (Expr t a f) (Expr u _ x)
  | a == 0 = ERROR "oversaturated function"
  | otherwise = Expr (App t u) (a - 1) (\env -> f env (x env))