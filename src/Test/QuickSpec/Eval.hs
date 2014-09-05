module Test.QuickSpec.Eval where

import Test.QuickSpec.Type
import Test.QuickSpec.Term 
import Test.QuickCheck

data Interpreted a = Interpreted {
  it :: a,
  interpretation :: Value Gen
  }

icon :: Typeable a => String -> a -> Interpreted Schema
icon name x =
  Interpreted {
    it = con name (typeOf x),
    interpretation = toValue (return x)
    }

ivar :: (Typeable a, Arbitrary a) => a -> Interpreted Schema
ivar x =
  Interpreted {
    it = var (typeOf x),
    interpretation = toValue (arbitrary `asTypeOf` return x)
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
