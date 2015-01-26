{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TypeOperators #-}
module Main where

import Prelude hiding (mapM)
import Test.QuickCheck hiding (output)
import QuickSpec hiding (size, (<+>), Poly)

type Z    = Int
type Poly = [Z]

data Matrix a = EM | CM a [a] [a] (Matrix a)
  deriving (Eq,Show)

class Ring a where
  (<+>) :: a -> a -> a
  (<*>) :: a -> a -> a
  neg   :: a -> a
  zero  :: a
  one   :: a

(<->) :: Ring a => a -> a -> a
a <-> b = a <+> neg b

infixl 7 <*>
infixl 6 <+>
infixl 6 <->

instance Ring Z where
  (<*>) = (*)
  (<+>) = (+)
  neg   = negate
  zero  = 0
  one   = 1

add_seq :: Poly -> Poly -> Poly
add_seq [] q = q
add_seq p [] = p
add_seq (x:xs) (y:ys) =
  let xy = x <+> y
      r  = add_seq xs ys
  in if xy == zero then if r == [] then [] else xy : r else xy : r

scale_seq :: Z -> Poly -> Poly
scale_seq _ [] = []
scale_seq x (hd : tl) =
  let r = scale_seq x tl
      xhd = x <*> hd
  in if xhd == zero then if r == [] then [] else xhd : r else xhd : r

shift :: Int -> Poly -> Poly
shift n [] = []
shift n p  = replicate n zero ++ p

mul_seq :: Poly -> Poly -> Poly
mul_seq [] q = []
mul_seq p [] = []
mul_seq (x:xs) q = add_seq (scale_seq x q) (mul_seq xs (shift 1 q))

instance Ring Poly where
  (<+>)  = add_seq
  (<*>)  = mul_seq
  neg    = map neg
  zero   = []
  one    = [one]

polyC_seq :: Z -> Poly
polyC_seq x = [x]

indet :: Int -> Poly
indet n = replicate n 0 ++ [1]

last' [] = 0
last' xs = last xs

-- Polynomial pseudo-division
edivp_rec_seq :: Poly -> Int -> Int -> Poly -> Poly -> ((Int,Poly),Poly)
edivp_rec_seq q = loop
  where
  sq = length q
  cq = last' q

  loop n k qq r =
    if length r < sq
       then ((k,qq),r)
       else let m   = (polyC_seq (last r)) <*> (indet (length r - sq))
                qq1 = (qq <*> (polyC_seq cq)) <+> m
                r1  = (r <*> (polyC_seq cq)) <-> (m <*> q)
            in if n == 0 then ((1 + k,qq1),r1) else loop (n - 1) (1 + k) qq1 r1

edivp_seq :: Poly -> Poly -> ((Int,Poly),Poly)
edivp_seq p q =
  if q == []
     then ((0,[]),p)
     else edivp_rec_seq q (length p) 0 [] p

divp_seq :: Poly -> Poly -> Poly
divp_seq p q = snd (fst (edivp_seq p q))

backgroundSig :: Signature
backgroundSig =
  signature {
    extraPruner = Just (SPASS 5),
    maxTermSize = Just 7,
    instances = [
      makeInstance (\() -> Observe (Dict :: Dict (Ord Poly)) (return . reverse . dropWhile (== 0) . reverse)) ],
    constants = [
      constant "0" (0 :: Int),
      constant "1" (1 :: Int),
      constant "+" ((+) :: Int -> Int -> Int),
      constant "*" ((*) :: Int -> Int -> Int),
      --constant "-" ((-) :: Int -> Int -> Int),
      constant "negate" (negate :: Int -> Int),
      constant "fst" (fst :: (A, B) -> A),
      constant "snd" (snd :: (A, B) -> B) ]}

polySig :: Signature
polySig =
  signature {
    extraPruner = Just (SPASS 5),
    constants = [
      constant "<+>" ((<+>) :: Poly -> Poly -> Poly),
      --constant "<->" ((<->) :: Poly -> Poly -> Poly),
      constant "<*>" ((<*>) :: Poly -> Poly -> Poly),
      constant "neg" (neg :: Poly -> Poly),
      constant "zero" (zero :: Poly),
      constant "one" (one :: Poly),
      constant "scale_seq" scale_seq,
      constant "shift" shift,
      constant "polyC_seq" polyC_seq,
      constant "indet" indet,
      constant "edivp_seq" edivp_seq,
      constant "divp_seq" divp_seq ]}

main = quickSpecWithBackground backgroundSig polySig

-- Functions on Matrix
adds :: Ring a => [a] -> [a] -> [a]
adds [] l2 = l2
adds l1 [] = l1
adds (x:l1) (y:l2) = x <+> y : adds l1 l2

addM :: Ring a => Matrix a -> Matrix a -> Matrix a
addM m1 m2 = case m1 of
  EM -> m2
  CM a1 l1 c1 m3 -> case m2 of
    EM -> m1
    CM a2 l2 c2 m4 -> CM (a1 <+> a2) (adds l1 l2) (adds c1 c2) (addM m3 m4)

mapM :: (a -> b) -> Matrix a -> Matrix b
mapM f m = case m of
  EM -> EM
  CM g l c m -> CM (f g) (map f l) (map f c) (mapM f m)

oppM :: Ring a => Matrix a -> Matrix a
oppM m = mapM neg m

subM :: Ring a => Matrix a -> Matrix a -> Matrix a
subM m n = addM m (oppM n)

multEM :: Ring a => a -> Matrix a -> Matrix a
multEM a m = case m of
  EM -> EM
  CM g l c m -> CM (a <*> g) (map (a <*>) l) (map (a <*>) c) (multEM a m)

mults :: Ring a => [a] -> [a] -> Matrix a
mults [] l = EM
mults u [] = EM
mults (u:us) (v:vs) =
  CM (u <*> v) (map (u <*>) vs) (map (v <*>) us) (mults us vs)

zeroes :: Ring a => Int -> [a]
zeroes n = replicate n zero

ident :: Ring a => Int -> Matrix a
ident 0 = EM
ident n = let p  = pred n
              zs = zeroes p
          in CM one zs zs (ident p)

-- Size of random matrices
size :: Int
size = 50

instance Arbitrary a => Arbitrary (Matrix a) where
  arbitrary = arb (size - 1)
    where
    arb' 0 = return []
    arb' n = do x  <- arbitrary
                xs <- arb' (n - 1)
                return (x : xs)

    arb 0 = return EM
    arb n | n < 0     = error "arbitrary: negative size"
          | otherwise = do a <- arbitrary
                           r <- arb' n
                           c <- arb' n
                           m <- arb (n - 1)
                           return $ CM a r c m

-- Generate a bunch of random matrices
-- sample (arbitrary :: Gen (Matrix Z))
