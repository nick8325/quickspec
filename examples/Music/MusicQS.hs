{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable, MultiParamTypeClasses, FlexibleInstances, GeneralizedNewtypeDeriving #-}
--module MusicQS where 

import Music hiding (main)
import Perform
import Test.QuickCheck
import Data.Ratio
import Control.Monad
import QuickSpec
import QuickSpec.Internal.Utils
import Data.Monoid
import Data.List
import qualified Data.Set as Set

deriving instance Typeable Positive

instance Arbitrary IName where
         arbitrary = oneof (map return [AcousticGrandPiano .. Percussion])
         shrink = genericShrink

instance Arbitrary PitchClass where
         arbitrary = oneof (map return [Cf .. Bs])
         shrink = genericShrink

-- Work around bad QuickCheck generator for rationals.
-- To do: fix this in QuickCheck!
genRatio :: Gen Rational
genRatio = do
  n <- sized $ \k -> choose (1, k `max` 1)
  m <- sized $ \k -> choose (0, n*k `max` 1)
  return (fromIntegral m/fromIntegral n)

instance Arbitrary Music where
         shrink = genericShrink
         arbitrary = sized arb' 
           where
                arb' 0 = oneof [liftM2 Note arbitrary genRatio,
                               liftM Rest genRatio]
                arb' n = oneof [liftM2 Note arbitrary genRatio,
                               liftM Rest genRatio,
                               liftM2 (:+:) submusic2 submusic2,
                               liftM2 (:=:) submusic2 submusic2,
                               liftM2 Tempo (genRatio `suchThat` (> 0)) submusic,
                               liftM2 Trans arbitrary submusic,
                               liftM2 Instr arbitrary submusic]
                       where submusic = arb' (n-1)
                             submusic2 = arb' (n `div` 2)

instance Arbitrary Context where
         shrink = genericShrink
         arbitrary = liftM4 Context arbitrary arbitrary (arbitrary `suchThat` (> 0)) arbitrary

instance Observe Context Performance Music where
  observe ctx m = usort (perform ctx (m :+: beep))
    where
      beep = Note (C, 4) 1

newtype NonNeg = NonNeg Rational deriving (Eq, Ord, Show, Num, Fractional)
instance Arbitrary NonNeg where arbitrary = NonNeg <$> genRatio
newtype Pos = Pos Rational deriving (Eq, Ord, Show, Num, Fractional)
instance Arbitrary Pos where arbitrary = Pos <$> (genRatio `suchThat` (> 0))

note :: Pitch -> NonNeg -> Music
note p (NonNeg x) = Note p x

rest :: NonNeg -> Music
rest (NonNeg x) = Rest x

tempo :: Pos -> Music -> Music
tempo (Pos x) m = Tempo x m

main = quickSpec [
  monoType (Proxy :: Proxy NonNeg),
  monoType (Proxy :: Proxy Pos),
  monoTypeWithVars ["p", "q", "r"] (Proxy :: Proxy Pitch),
  monoTypeObserveWithVars ["m", "n", "o"] (Proxy :: Proxy Music),

  background bg,
  series [sig1, sig2, sig3] ]
  where
    bg = [
      arith (Proxy :: Proxy NonNeg),
      arith (Proxy :: Proxy Pos) `without` ["0"],
      con "*" ((*) :: Pos -> Pos -> Pos),
      con "/" ((/) :: Pos -> Pos -> Pos),
      con "max" (max :: NonNeg -> NonNeg -> NonNeg),
      con "" (\(Pos x) -> NonNeg x) ]

    sig1 = [ con "Note" note,
             con "Rest" rest,
             con ":+:" (:+:) ]
    sig2 = [ con ":=:" (:=:) ]
    sig3 = [ con "Tempo" tempo ]
