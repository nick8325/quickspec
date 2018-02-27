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

main = quickSpec [
  withMaxTermSize 10,
  monoTypeWithVars ["x", "y", "z"] (Proxy :: Proxy NonZero),
  monoTypeWithVars ["x", "y", "z"] (Proxy :: Proxy Odd),
  con "1" (1 :: Int),
  con "1" (NonZero 1),
  con "1" (Odd 1),
  con "0" (0 :: Int),
  con "nonZeroInt" nonZeroInt,
  con "oddInt"     oddInt,
  con "oddNonZero" oddNonZero,
  con "divide"     divide ]
