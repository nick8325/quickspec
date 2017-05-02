{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP #-}
module QuickSpec.Parse where

#include "errors.h"
import Control.Applicative
import Control.Monad
import Data.Char
import qualified Data.Map as Map
import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import qualified Twee.Label as Label
import Text.ParserCombinators.ReadP
import Data.List
import Twee.Base hiding (char)
import Data.Maybe

class Parse a where
  parse :: [Constant] -> ReadP a

newtype StringVar = StringVar String deriving (Eq, Ord, Show)

instance Label.Labelled StringVar where
  cache = stringVarCache

{-# NOINLINE stringVarCache #-}
stringVarCache :: Label.Cache StringVar
stringVarCache = Label.mkCache

instance Parse Var where
  parse cs = do
    x <- satisfy isUpper
    xs <- munch isAlphaNum
    guard ((x:xs) `notElem` map conName cs)
    return (MkVar (Label.label (StringVar (x:xs))))

instance Parse Constant where
  parse cs = do
    name <- munch1 (\c -> c `notElem` "(),")
    case [ c | c <- cs, conName c == name ] of
      [c] -> return c
      _   -> pfail

instance Parse (Term Constant) where
  parse cs =
    fmap typedVar (parse cs) <++ do
      f <- parse cs
      args <- parseArgs <++ return []
      return (unPoly (foldl apply (poly (app f [])) (map poly args)))
    where
      parseArgs = between (char '(') (char ')') (sepBy (parse cs) (char ','))
      typedVar x = app (Id (typeOf (undefined :: A))) [build (var x)]

instance Parse (Literal (Term Constant)) where
  parse cs = equality <++ predicate
    where
      equality = do
        t <- parse cs
        string "="
        u <- parse cs
        let eqv = toValue (return (undefined :: A -> A -> Bool))
            eq = Constant "eq" eqv (poly eqv) 0 undefined undefined undefined
            App _ [t', u'] = unPoly (foldl apply (poly (app eq [])) [poly t, poly u])
        return (t' :=: u')
      predicate = do
        t@(App f ts) <- parse cs
        guard (typ t == typeOf (undefined :: Bool))
        let p = Predicate (conName f) (termStyle f) (typ f) (polyTyp (conGeneralValue f))
        return (p :@: ts)

instance Parse (PropOf (Term Constant)) where
  parse cs = do
    lhs <- sepBy (parse cs) (string "&")
    unless (null lhs) (void (string "=>"))
    rhs <- parse cs
    return (lhs :=>: rhs)

parseProp :: (Parse a, Show a) => [Constant] -> String -> a
parseProp cs xs =
  case readP_to_S (parse cs <* eof) (filter (not . isSpace) xs) of
    [(x, [])] -> x
    ps -> error ("parse': got result " ++ show ps ++ " while parsing " ++ xs)

showTheory :: [Prop] -> String
showTheory thy =
  "background = [\n" ++
  intercalate ",\n" ["  \"" ++ escape (prettyShow p) ++ "\"" | p <- thy ] ++ "]"
  where
    escape = concatMap f
    f '"' = "\\\""
    f x = [x]
