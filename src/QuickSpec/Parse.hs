-- | Parsing strings into properties.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module QuickSpec.Parse where

import Control.Monad
import Data.Char
import QuickSpec.Prop
import QuickSpec.Term hiding (char)
import QuickSpec.Type
import qualified Twee.Label as Label
import Text.ParserCombinators.ReadP

class Parse fun a where
  parse :: ReadP fun -> ReadP a

instance Parse fun Var where
  parse _ = do
    x <- satisfy isUpper
    xs <- munch isAlphaNum
    let name = x:xs
    -- Use Twee.Label as an easy way to generate a variable number
    return (V typeVar (fromIntegral (Label.labelNum (Label.label name))))

instance (fun1 ~ fun, Apply (Term fun)) => Parse fun1 (Term fun) where
  parse pfun =
    parseApp <++ parseVar
    where
      parseVar = Var <$> parse pfun
      parseApp = do
        f <- pfun
        args <- parseArgs <++ return []
        return (unPoly (foldl apply (poly (App f [])) (map poly args)))
      parseArgs = between (char '(') (char ')') (sepBy (parse pfun) (char ','))

instance (Parse fun a, Typed a) => Parse fun (Equation a) where
  parse pfun = do
    t <- parse pfun
    string "="
    u <- parse pfun
    -- Compute type unifier of t and u
    -- "maybe mzero return" injects Maybe into MonadPlus
    pt <- maybe mzero return (polyMgu (poly (typ t)) (poly (typ u)))
    t <- maybe mzero return (cast (unPoly pt) t)
    u <- maybe mzero return (cast (unPoly pt) u)
    return (t :=: u)

instance (Parse fun a, Typed a) => Parse fun (Prop a) where
  parse pfun = do
    lhs <- sepBy (parse pfun) (string "&")
    unless (null lhs) (void (string "=>"))
    rhs <- parse pfun
    return (lhs :=>: rhs)

parseProp :: (Parse fun a, Pretty a) => ReadP fun -> String -> a
parseProp pfun xs =
  case readP_to_S (parse pfun <* eof) (filter (not . isSpace) xs) of
    [(x, [])] -> x
    ps -> error ("parse': got result " ++ prettyShow ps ++ " while parsing " ++ xs)
