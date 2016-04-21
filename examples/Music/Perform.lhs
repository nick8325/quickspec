> {-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

This code was automatically extracted from a .lhs file that
uses the following convention:

-- lines beginning with ">" are executable
-- lines beginning with "<" are in the text,
     but not necessarily executable


-- lines beginning with "|" are also in the text,
     but are often just expressions or code fragments.

> module Perform where
>
> import Music
> import GHC.Generics
> import Data.Ratio
> import Data.Typeable

> type Performance = [Event]
>
> data Event = Event { eTime :: Time, eInst :: IName, 
>                      ePitch :: AbsPitch, eDur  :: DurT }
>      deriving (Eq,Ord,Show, Typeable)
>
> type Time      = Rational
> type DurT      = Rational

< perform :: Context -> Music -> Performance

> data Context = Context { cTime :: Time, cInst :: IName,
>                          cDur  :: DurT, cKey  :: Key }
>   deriving (Show,Generic,Typeable)
>
> type Key     = AbsPitch

> metro :: Rational -> Dur -> DurT
> metro setting dur = 60 / (setting * ratioToRational dur)

> ratioToRational  :: Rational -> Rational
> ratioToRational r = r

> intToRational :: Int -> Rational
> intToRational  = fromInteger . toInteger

< perform c@(Context t i dt k) m =
<  case m of
<     Note p d    -> let d' = ratioToRational d * dt
<                    in [Event t i (transpose p k i) d']
<     Rest d      -> []
<     m1 :+: m2   -> perform c m1 ++ 
<                    perform 
<                     (c {cTime = t + ratioToRational (dur m1) * dt}) m2
<     m1 :=: m2   -> merge (perform c m1) (perform c m2)
<     Tempo  a  m -> perform (c {cDur = dt / ratioToRational a}) m
<     Trans  p  m -> perform (c {cKey = k + p}) m
<     Instr  nm m -> perform (c {cInst = nm}) m
<  where transpose p k Percussion = absPitch p
<        transpose p k _          = absPitch p + k

> merge :: Performance -> Performance -> Performance

> merge a@(e1:es1) b@(e2:es2) = 
>      if e1 < e2 then e1 : merge es1 b
>                 else e2 : merge a es2
> merge [] es2 = es2
> merge es1 [] = es1

< merge a@(e1:es1) b@(e2:es2) =
<   if eTime e1 < eTime e2 then e1 : merge es1 b
<                          else e2 : merge a es2
< merge [] es2 = es2
< merge es1 [] = es1

> perform :: Context -> Music -> Performance
> perform c m = fst (perf c m)
>
> perf :: Context -> Music -> (Performance, DurT)

> perf c@(Context t i dt k) m =
>   case m of
>     Note p d     -> let d' = ratioToRational d * dt
>                     in ([Event t i (transpose p k i) d'], d')
>     Rest d       -> ([], ratioToRational d * dt)
>     m1 :+: m2    -> let (pf1,d1) = perf c m1
>                         (pf2,d2) = perf (c {cTime = t+d1}) m2
>                     in (pf1++pf2, d1+d2)
>     m1 :=: m2    -> let (pf1,d1) = perf c m1
>                         (pf2,d2) = perf c m2
>                     in (merge pf1 pf2, max d1 d2)
>     Tempo  a  m  -> perf (c {cDur = dt / ratioToRational a}) m
>     Trans  p  m  -> perf (c {cKey = k + p}) m
>     Instr  nm m  -> perf (c {cInst = nm}) m
>   where transpose p k Percussion = absPitch p
>         transpose p k _          = absPitch p + k

| (m1 :+: m2) :+: m3
| m1 :+: (m2 :+: m3)

| Tempo r1 (Tempo r2 m) === Tempo (r1*r2) m

| perform dt (Tempo r1 (Tempo r2 m))
| ==> { <<< unfold >>> perform <<< >>> }
| perform (dt/rtf r1) (Tempo r2 m)
| ==> { <<< unfold >>> perform <<< >>> }
| perform ((dt/rtf r1)/(rtf r2)) m
| ==> { <<< arithmetic >>> }
| perform (dt/((rtf r1)*(rtf r2))) m
| ==> { <<< lemma for >>> ratioToFLoat <<< >>> }
| perform (dt/(rtf (r1*r2))) m
| ==> { <<< fold >>> perform <<< >>> }
| perform dt (Tempo (r1*r2) m)

| Tempo r (m1 :+: m2) === Tempo r m1 :+: Tempo r m2

| perform (t,dt) (Tempo r (m1 :+: m2))
| ==> { <<< unfold >>> perform <<< >>> }
| perform (t,dt/rtf r) (m1 :+: m2)
| ==> { <<< unfold >>> perform <<< >>> }
| perform (t,dt/rtf r) m1 ++ perform (t1,dt/rtf r) m2
| ==> { <<< fold >>> perform <<< >>> }
| perform (t,dt) (Tempo r m1) ++ perform (t1,dt) (Tempo r m2)
| ==> { <<< arithmetic >>> }
| perform (t,dt) (Tempo r m1) ++ perform (t2,dt) (Tempo r m2)
| ==> { <<< fold >>> dur <<< >>> }
| perform (t,dt) (Tempo r m1) ++ perform (t3,dt) (Tempo r m2)
| ==> { <<< fold >>> perform <<< >>> }
| perform (t,dt) (Tempo r m1 :+: Tempo r m2)
|   where t1 = t + rtf (dur m1) * (dt/rtf r)
|         t2 = t + rtf (dur m1 / r) * dt
|         t3 = t + rtf (dur (Tempo r m1)) * dt

| Tempo 1 m === m

| perform (t,dt) (Tempo 1 m)
| ==> { <<< unfold >>> perform <<< >>> }
| perform (t,dt/rtf 1) m
| ==> { <<< arithmetic >>> }
| perform (t,dt) m

| Tempo r m1 :+: m2 === Tempo r (m1 :+: Tempo (1/r) m2)

| Tempo r (m1 :+: Tempo (1/r) m2)
| ==> { <<< by Axiom 2 >>> }
| Tempo r m1 :+: Tempo r (Tempo (1/r) m2)
| ==> { <<< by Axiom 1 >>> }
| Tempo r m1 :+: Tempo (r*(1/r)) m2
| ==> { <<< arithmetic >>> }
| Tempo r m1 :+: Tempo 1 m2
| ==> { <<< by Axiom 3 >>> }
| Tempo r m1 :+: m2

| Tempo r1 (Tempo r2 m) === Tempo (r1*r2) m
| Trans p1 (Trans p2 m) === Trans (p1+p2) m

| Tempo r1 . Tempo r2 === Tempo r2 . Tempo r1
| Trans p1 . Trans p2 === Trans p2 . Trans p1
| Tempo r1 . Trans p1 === Trans p1 . Tempo r1

| Tempo r (m1 :+: m2) === Tempo r m1 :+: Tempo r m2
| Tempo r (m1 :=: m2) === Tempo r m1 :=: Tempo r m2
| Trans p (m1 :+: m2) === Trans p m1 :+: Trans p m2
| Trans p (m1 :=: m2) === Trans p m1 :=: Trans p m2

| m0 :+: (m1 :+: m2) === (m0 :+: m1) :+: m2
| m0 :=: (m1 :=: m2) === (m0 :=: m1) :=: m2

| m0 :=: m1 === m1 :=: m0

| Tempo r (Rest 0) === Rest 0
| Trans p (Rest 0) === Rest 0
| m :+: Rest 0 === m === Rest 0 :+: m
| m :=: Rest 0 === m === Rest 0 :=: m 

| (m0 :+: m1) :=: (m2 :+: m3) === (m0 :=: m2) :+: (m1 :=: m3)

| revM (revM m) === m

