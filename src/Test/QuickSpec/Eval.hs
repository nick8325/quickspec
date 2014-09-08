module Test.QuickSpec.Eval where

import Test.QuickSpec.Type
import Test.QuickSpec.Term 
import Test.QuickCheck
import qualified Data.Typeable as T
import qualified Data.Typeable.Internal as T

data Interpreted a = Interpreted {
  it :: a,
  interpretation :: Value Gen
  }

icon :: Typeable a => String -> a -> Interpreted (TmOf v)
icon name x =
  Interpreted {
    it = con name (typeOf x),
    interpretation = toValue (return x)
    }

ihole :: (Typeable a, Arbitrary a) => a -> Interpreted Schema
ihole x =
  Interpreted {
    it = hole (typeOf x),
    interpretation = toValue (coarbitrary (T.typeOf x) arbitrary `asTypeOf` return x)
    }
instance CoArbitrary T.TypeRep where
  coarbitrary (T.TypeRep x _ _) = coarbitrary x
instance CoArbitrary T.Fingerprint where
  coarbitrary (T.Fingerprint x y) = coarbitrary (x, y)

ivar :: (Typeable a, Arbitrary a) => a -> Int -> Interpreted Tm
ivar x n =
  Interpreted {
    it = var (typeOf x) n,
    interpretation = toValue (variant n arbitrary `asTypeOf` return x)
    }

instance TyVars a => TyVars (Interpreted a) where
  tyVars x = tyVars (it x)
  tySubst f x = x { it = tySubst f (it x) }

instance Apply a => Apply (Interpreted a) where
  tyApply f x = do
    (fIt, xIt) <- tyApply (it f) (it x)
    (fInt, xInt) <- tyApply (interpretation f) (interpretation x)
    return (Interpreted fIt fInt,
            Interpreted xIt xInt)
  tyGroundApply f x =
    Interpreted {
      it = tyGroundApply (it f) (it x),
      interpretation = tyGroundApply (interpretation f) (interpretation x)
      }
