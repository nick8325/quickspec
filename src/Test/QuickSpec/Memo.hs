{-# LANGUAGE TypeOperators, Rank2Types, FlexibleContexts, TypeSynonymInstances, StandaloneDeriving, DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Test.QuickSpec.Memo where

import GHC.Generics
import Data.MemoCombinators
import Data.MemoCombinators.Class
import Prelude hiding (either)
import Test.QuickSpec.Base
import Test.QuickSpec.Type(TyCon(..), TyVar(..))
import qualified Data.Typeable as T
import qualified Data.Typeable.Internal as T
import Data.Word

genericTable :: (Generic a, GMemoTable (Rep a)) => Memo a
genericTable = wrap to from gtable

class GMemoTable f where
  gtable :: Memo (f a)

instance (GMemoTable f, GMemoTable g) => GMemoTable (f :*: g) where
  gtable =
    wrap
      (\(x, y) -> x :*: y)
      (\(x :*: y) -> (x, y))
      (pair gtable gtable)

instance (GMemoTable f, GMemoTable g) => GMemoTable (f :+: g) where
  gtable = wrap f g (either gtable gtable)
    where
      f (Left x) = L1 x
      f (Right x) = R1 x
      g (L1 x) = Left x
      g (R1 x) = Right x

instance GMemoTable f => GMemoTable (M1 i c f) where
  gtable = wrap M1 (\(M1 x) -> x) gtable

instance MemoTable a => GMemoTable (K1 i a) where
  gtable = wrap K1 (\(K1 x) -> x) table

instance GMemoTable U1 where
  gtable = wrap (\() -> U1) (\U1 -> ()) table

deriving instance Generic (Tm f v)
deriving instance Generic TyCon
deriving instance Generic TyVar
instance (MemoTable f, MemoTable v) => MemoTable (Tm f v) where table = genericTable
instance MemoTable TyCon where table = genericTable
instance MemoTable TyVar where table = genericTable
instance MemoTable T.TyCon where
  table = wrap f g table
    where
      f :: (Word64, Word64) -> T.TyCon
      f (x, y) = T.TyCon (T.Fingerprint x y) undefined undefined undefined
      g :: T.TyCon -> (Word64, Word64)
      g (T.TyCon (T.Fingerprint x y) _ _ _) = (x, y)
