module QuickSpec.NamesFor where

import Data.Typeable

newtype NamesFor a = NamesFor { unNamesFor :: [String] } deriving Typeable
