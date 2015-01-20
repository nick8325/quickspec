{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP #-}
module QuickSpec.Parse where

#include "errors.h"
import Control.Applicative
import Control.Monad
import Data.Char
import qualified Data.Map as Map
import QuickSpec.Base hiding (char)
import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import Text.ParserCombinators.ReadP
import Data.List

class Parse a where
  parse :: [Constant] -> ReadP a

data StringVar = StringVar String Type deriving (Eq, Ord, Show)

instance Typed StringVar where
  typ (StringVar _ ty) = ty
  typeSubst sub (StringVar name ty) = StringVar name (typeSubst sub ty)

instance Parse StringVar where
  parse cs = do
    x <- satisfy isUpper
    xs <- munch isAlphaNum
    guard ((x:xs) `notElem` map conName cs)
    return (StringVar (x:xs) (typeOf (undefined :: A)))

instance Parse Constant where
  parse cs = do
    name <- munch1 (\c -> c `notElem` "(),")
    case [ c | c <- cs, conName c == name ] of
      [c] -> return c
      _   -> pfail

instance (Typed v, Parse v) => Parse (TermOf v) where
  parse cs =
    fmap Var (parse cs) <++ do
      f <- parse cs
      args <- parseArgs <++ return []
      return (unPoly (foldl apply (poly (Fun f [])) (map poly args)))
    where
      parseArgs = between (char '(') (char ')') (sepBy (parse cs) (char ','))

instance (Typed v, Parse v) => Parse (Literal (TermOf v)) where
  parse cs = equality <++ predicate
    where
      equality = do
        t <- parse cs
        string "="
        u <- parse cs
        let eqv = toValue (return (undefined :: A -> A -> Bool))
            eq = Constant "eq" eqv (poly eqv) 0 undefined undefined undefined
            Fun _ [t', u'] = unPoly (foldl apply (poly (Fun eq [])) [poly t, poly u])
        return (t' :=: u')
      predicate = do
        t@(Fun f ts) <- parse cs
        guard (typ t == typeOf (undefined :: Bool))
        let p = Predicate (conName f) (typ f)
        return (p :@: ts)

instance (Typed v, Parse v) => Parse (PropOf (TermOf v)) where
  parse cs = do
    lhs <- sepBy (parse cs) (string "&")
    unless (null lhs) (void (string "=>"))
    rhs <- parse cs
    return (lhs :=>: rhs)

parse' :: (Parse a, Show a) => [Constant] -> String -> a
parse' cs xs =
  case readP_to_S (parse cs <* eof) (filter (not . isSpace) xs) of
    [(x, [])] -> x
    ps -> error ("parse': got result " ++ show ps ++ " while parsing " ++ xs)

parseProp :: [Constant] -> String -> Prop
parseProp cs xs = toProp (parse' cs xs)

toProp :: PropOf (TermOf StringVar) -> Prop
toProp prop = fmap (rename (\x -> Variable (Map.findWithDefault __ x sub) (typ x))) prop
  where
    vs = usort (vars prop)
    sub = Map.fromList (zip vs [0..])

fromProp :: Prop -> PropOf (TermOf StringVar)
fromProp prop = fmap (rename (\x -> StringVar (Map.findWithDefault __ x sub) (typ x))) prop
  where
    vs = nub (vars prop)
    sub = Map.fromList (zip vs [ "X" ++ show x | x <- [1..] ])

showProp :: PropOf (Tm Constant StringVar) -> String
showProp ([] :=>: rhs) = showLiteral rhs
showProp (lhs :=>: rhs) =
  intercalate " & " (map showLiteral lhs) ++ " => " ++ showLiteral rhs

showLiteral :: Literal (Tm Constant StringVar) -> String
showLiteral (p :@: []) = predName p
showLiteral (p :@: ts) = predName p ++ "(" ++ intercalate ", " (map showTerm ts) ++ ")"
showLiteral (t :=: u) = showTerm t ++ " = " ++ showTerm u

showTerm :: Tm Constant StringVar -> String
showTerm (Var (StringVar x _)) = x
showTerm (Fun f []) = conName f
showTerm (Fun f ts) = conName f ++ "(" ++ intercalate ", " (map showTerm ts) ++ ")"

showTheory :: [Prop] -> String
showTheory thy =
  "background = [\n" ++
  intercalate ",\n" ["  \"" ++ escape (showProp (fromProp p)) ++ "\"" | p <- thy ] ++ "]"
  where
    escape = concatMap f
    f '"' = "\\\""
    f x = [x]
