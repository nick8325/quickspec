import QuickSpec
import Test.QuickCheck hiding (NonZero)

{- The universe of types -}

{- type NonZero = { x : Int | x /= 0 } -}
newtype NonZero = NonZero Int deriving (Ord, Eq, Show)

instance Arbitrary NonZero where
  arbitrary = NonZero <$> arbitrary `suchThat` (/= 0)

{- type Odd = { x : Int | odd x } -}
newtype Odd = Odd Int deriving (Ord, Eq, Show)

instance Arbitrary Odd where
  arbitrary = Odd <$> arbitrary `suchThat` odd

{- NonZero <= Int -}
nonZeroInt :: NonZero -> Int 
nonZeroInt (NonZero i) = i

{- Odd <= Int -}
oddInt :: Odd -> Int
oddInt (Odd i) = i

{- Odd <= NonZero -}
oddNonZero :: Odd -> NonZero
oddNonZero (Odd i) = NonZero i

{- The functions of interest -}

divide :: Int -> NonZero -> Int
divide i (NonZero j) = div i j

sig =
  signature {
    maxTermSize = Just 10,
    instances   = [ 
                    baseTypeNames ["x", "y", "z"] (undefined :: NonZero),
                    baseTypeNames ["x", "y", "z"] (undefined :: Odd)
    ],
    constants   = [
      constant "1" (1 :: Int),
      constant "1" (NonZero 1),
      constant "1" (Odd 1),
      constant "0" (0 :: Int),
      constant "nonZeroInt" nonZeroInt,
      constant "oddInt"     oddInt,
      constant "oddNonZero" oddNonZero,
      constant "divide"     divide
    ]
   }

main = quickSpec sig
