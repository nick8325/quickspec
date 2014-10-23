{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP #-}
module QuickSpec.Parse where

#include "errors.h"
import Text.ParserCombinators.ReadP
import Data.Char
import QuickSpec.Signature
import QuickSpec.Type
import QuickSpec.Term
import QuickSpec.Base hiding (char)
import QuickSpec.Utils
import QuickSpec.Prop
import Control.Monad
import Control.Applicative
import qualified Data.Map as Map

class Parse a where
  parse :: [Constant] -> ReadP a

data StringVar = StringVar String Type deriving (Eq, Ord, Show)

instance Typed StringVar where
  typ (StringVar _ ty) = ty
  typeSubstA f (StringVar name ty) =
    liftM (StringVar name) (typeSubstA f ty)

instance Parse StringVar where
  parse _ = do
    x <- satisfy isUpper
    xs <- munch isAlphaNum
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
        return (t :=: u)
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
    ps -> error ("parse': got result " ++ show ps)

parseProp :: [Constant] -> String -> Prop
parseProp cs xs = toProp (parse' cs xs)

toProp :: PropOf (TermOf StringVar) -> Prop
toProp prop = fmap (rename (\x -> Variable (Map.findWithDefault __ x sub) (typ x))) prop
  where
    vs = usort (concatMap vars (propTerms prop))
    sub = Map.fromList (zip vs [0..])
