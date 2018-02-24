-- a function which satisfies x+(y+z)=y+(x+z) but is not AC
import QuickSpec
import Test.QuickCheck

data X = A | B | C deriving (Eq, Ord, Enum, Bounded)
instance Arbitrary X where arbitrary = elements [minBound..maxBound]

funny :: (X, X) -> X
funny(A,A) = C
funny(A,B) = A
funny(A,C) = B
funny(B,A) = C
funny(B,B) = A
funny(B,C) = B
funny(C,A) = B
funny(C,B) = C
funny(C,C) = A

main = quickSpec [monoType (Proxy :: Proxy X), con "+" (curry funny)]
