module QuickSpec.Pretty where

import Text.PrettyPrint.HughesPJ
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)

class Pretty a where
  pretty :: a -> Doc
  pretty = prettyPrec 0

  prettyPrec :: Int -> a -> Doc
  prettyPrec _ = pretty
  
  prettyList :: [a] -> Doc
  prettyList = brackets . fsep . punctuate comma . map pretty

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

instance Pretty a => Pretty (Maybe a) where
  prettyPrec p (Just x) =
    prettyParen (p > 11) $
      hang (text "Just") 2 (prettyPrec 11 x)
  prettyPrec _ Nothing = text "Nothing"

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

supply :: [String] -> [String]
supply names =
  names ++
  [ name ++ show i | i <- [2..], name <- names ]
