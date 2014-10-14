module QuickSpec.Pretty where

import Text.PrettyPrint.HughesPJ
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)

class Pretty a where
  pretty :: a -> Doc
  pretty x = prettyPrecApp 0 x []

  prettyPrec :: Integer -> a -> Doc
  prettyPrec _ = pretty
  
  prettyList :: [a] -> Doc
  prettyList = brackets . fsep . punctuate comma . map pretty

  prettyPrecApp :: Integer -> a -> [Integer -> Doc] -> Doc
  prettyPrecApp p x = prettyPrecGenericApp p (prettyPrec p x)

prettyPrecGenericApp :: Integer -> Doc -> [Integer -> Doc] -> Doc
prettyPrecGenericApp p d [] = d
prettyPrecGenericApp p d xs =
  prettyParen (p > 10) $
    hang d 2
      (fsep (map ($ 11) xs))

prettyPrecUncurriedApp :: Integer -> Doc -> [Integer -> Doc] -> Doc
prettyPrecUncurriedApp _ d [] = d
prettyPrecUncurriedApp _ d xs =
  d <> parens (fsep (map ($ 0) xs))

instance Pretty Int where pretty = int
instance Pretty Integer where pretty = integer
instance Pretty () where pretty = text . show
instance Pretty a => Pretty [a] where pretty = prettyList
instance Pretty Char where
  pretty = char
  prettyList = text . show

instance (Pretty a, Pretty b) => Pretty (a, b) where
  pretty (x, y) = prettyTuple [pretty x, pretty y]
instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  pretty (x, y, z) = prettyTuple [pretty x, pretty y, pretty z]
instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty (a, b, c, d) where
  pretty (x, y, z, w) = prettyTuple [pretty x, pretty y, pretty z, pretty w]

prettyTuple :: [Doc] -> Doc
prettyTuple = parens . fsep . punctuate comma

prettyParen :: Bool -> Doc -> Doc
prettyParen True  d = parens d
prettyParen False d = d

prettyPrint :: Pretty a => a -> IO ()
prettyPrint x = putStrLn (prettyShow x)

prettyShow :: Pretty a => a -> String
prettyShow = show . pretty

instance Pretty a => Pretty (Set a) where
  pretty = prettySet . map pretty . Set.toList

prettySet :: [Doc] -> Doc
prettySet = braces . fsep . punctuate comma

instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pretty = prettySet . map binding . Map.toList
    where
      binding (x, v) = hang (pretty x <+> text "=>") 2 (pretty v)

tupleOp :: Int -> Doc -> Integer -> [Integer -> Doc] -> Doc
tupleOp arity d p xs
  | length xs >= arity =
    prettyPrecGenericApp p
      (prettyTuple (take arity (map ($ 0) xs)))
      (drop arity xs)
  | otherwise =
    prettyPrecGenericApp p
      (text ("(" ++ replicate arity ',' ++ ")"))
      xs

infixOp :: Integer -> Doc -> Integer -> [Integer -> Doc] -> Doc
infixOp = infixOp' 1 1

infixOp' :: Integer -> Integer -> Integer -> Doc -> Integer -> [Integer -> Doc] -> Doc
infixOp' l r pOp d p [x, y] =
  prettyParen (p > pOp) $
    hang (x (pOp+l) <+> d) 2
         (y (pOp+r))
infixOp' l r pOp d p xs =
  prettyParen (p > pOp) $
    hang (parens d) 2
      (fsep (map ($ 11) xs))

supply :: [String] -> [String]
supply names =
  names ++
  [ name ++ show i | i <- [2..], name <- names ]
