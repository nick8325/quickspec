> {-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}


This code was automatically extracted from a .lhs file that
uses the following convention:

-- lines beginning with ">" are executable
-- lines beginning with "<" are in the text,
     but not necessarily executable
-- lines beginning with "|" are also in the text,
     but are often just expressions or code fragments.

| testWin95 m 
| testNT    m 
| testLinux m 

> module Music where
> import Data.Ratio
> import GHC.Generics
> import Data.Typeable

> type Pitch      = (PitchClass, Octave)
> data PitchClass = Cf | C | Cs | Df | D | Ds | Ef | E | Es | Ff | F 
>                 | Fs | Gf | G | Gs | Af | A | As | Bf | B | Bs
>      deriving (Eq,Show,Enum,Typeable, Ord, Generic)
> type Octave     = Int

> data Music = Note Pitch Dur
>            | Rest Dur
>            | Music :+: Music
>            | Music :=: Music
>            | Tempo  (Ratio Int) Music
>            | Trans  Int Music
>            | Instr  IName Music
>     deriving (Show, Eq, Typeable,Generic)
>
> type Dur   = Ratio Int

> data IName 
>  = AcousticGrandPiano  | BrightAcousticPiano | ElectricGrandPiano
>  | HonkyTonkPiano      | RhodesPiano         | ChorusedPiano
>  | Harpsichord   | Clavinet        | Celesta | Glockenspiel  | MusicBox
>  | Vibraphone | Marimba  | Xylophone           | TubularBells
>  | Dulcimer              | HammondOrgan        | PercussiveOrgan 
>  | RockOrgan | ChurchOrgan         | ReedOrgan
>  | Accordion             | Harmonica           | TangoAccordion
>  | AcousticGuitarNylon   | AcousticGuitarSteel | ElectricGuitarJazz
>  | ElectricGuitarClean   | ElectricGuitarMuted | OverdrivenGuitar
>  | DistortionGuitar      | GuitarHarmonics     | AcousticBass
>  | ElectricBassFingered  | ElectricBassPicked  | FretlessBass
>  | SlapBass1             | SlapBass2           | SynthBass1 | SynthBass2
>  | Violin        | Viola | Cello  | Contrabass | TremoloStrings
>  | PizzicatoStrings      | OrchestralHarp      | Timpani
>  | StringEnsemble1       | StringEnsemble2     | SynthStrings1
>  | SynthStrings2         | ChoirAahs           | VoiceOohs | SynthVoice
>  | OrchestraHit          | Trumpet             | Trombone  | Tuba 
>  | MutedTrumpet          | FrenchHorn          | BrassSection | SynthBrass1
>  | SynthBrass2           | SopranoSax          | AltoSax | TenorSax 
>  | BaritoneSax    | Oboe | Bassoon  | EnglishHorn          | Clarinet
>  | Piccolo               | Flute    | Recorder | PanFlute  | BlownBottle
>  | Shakuhachi            | Whistle  | Ocarina  | Lead1Square
>  | Lead2Sawtooth         | Lead3Calliope       | Lead4Chiff
>  | Lead5Charang          | Lead6Voice          | Lead7Fifths
>  | Lead8BassLead         | Pad1NewAge          | Pad2Warm
>  | Pad3Polysynth         | Pad4Choir           | Pad5Bowed
>  | Pad6Metallic          | Pad7Halo            | Pad8Sweep
>  | FX1Train              | FX2Soundtrack       | FX3Crystal
>  | FX4Atmosphere         | FX5Brightness       | FX6Goblins
>  | FX7Echoes             | FX8SciFi            | Sitar | Banjo  | Shamisen
>  | Koto | Kalimba        | Bagpipe             | Fiddle | Shanai
>  | TinkleBell    | Agogo | SteelDrums          | Woodblock      | TaikoDrum
>  | MelodicDrum           | SynthDrum           | ReverseCymbal
>  | GuitarFretNoise       | BreathNoise         | Seashore
>  | BirdTweet             | TelephoneRing       | Helicopter
>  | Applause              | Gunshot             | Percussion
>  deriving (Show,Eq,Ord,Enum,Typeable,Generic)

> 
> type AbsPitch = Int

> absPitch :: Pitch -> AbsPitch
> absPitch (pc,oct) = 12*oct + pcToInt pc

> pitch    :: AbsPitch -> Pitch
> pitch ap = ( [C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! mod ap 12,
>              quot ap 12 )

> pcToInt :: PitchClass -> Int
> pcToInt pc = case pc of
>                Cf -> -1   -- should Cf be 11?
>                C  -> 0  
>                Cs -> 1
>                Df -> 1
>                D  -> 2
>                Ds -> 3
>                Ef -> 3
>                E  -> 4
>                Es -> 5
>                Ff -> 4
>                F  -> 5
>                Fs -> 6
>                Gf -> 6
>                G  -> 7
>                Gs -> 8
>                Af -> 8
>                A  -> 9
>                As -> 10
>                Bf -> 10
>                B  -> 11
>                Bs -> 12 -- should Bs be 0?

< infixl 9  !!
< (!!)                :: [a] -> Int -> a
< (x:_)  !! 0         =  x
< (_:xs) !! n | n > 0 =  xs !! (n-1)
< (_:_)  !! _         =  error "PreludeList.!!: negative index"
< []     !! _         =  error "PreludeList.!!: index too large"

> trans    :: Int -> Pitch -> Pitch
> trans i p = pitch (absPitch p + i)

> cf,c,cs,df,d,ds,ef,e,es,ff,f,fs,gf,g,gs,af,a,as,bf,b,bs 
>   :: Octave -> Dur -> Music

> cf o = Note (Cf,o);  c o = Note (C,o);  cs o = Note (Cs,o)
> df o = Note (Df,o);  d o = Note (D,o);  ds o = Note (Ds,o)
> ef o = Note (Ef,o);  e o = Note (E,o);  es o = Note (Es,o)
> ff o = Note (Ff,o);  f o = Note (F,o);  fs o = Note (Fs,o)
> gf o = Note (Gf,o);  g o = Note (G,o);  gs o = Note (Gs,o)
> af o = Note (Af,o);  a o = Note (A,o);  as o = Note (As,o)
> bf o = Note (Bf,o);  b o = Note (B,o);  bs o = Note (Bs,o)

> wn,  hn,  qn,  en,  sn,  tn  :: Dur
> dhn, dqn, den, dsn           :: Dur
>
> wnr, hnr, qnr, enr, snr, tnr :: Music
> dhnr, dqnr, denr, dsnr       :: Music

> wn  = 1         ; wnr  = Rest wn      -- whole
> hn  = 1%2       ; hnr  = Rest hn      -- half
> qn  = 1%4       ; qnr  = Rest qn      -- quarter
> en  = 1%8       ; enr  = Rest en      -- eight
> sn  = 1%16      ; snr  = Rest sn      -- sixteenth
> tn  = 1%32      ; tnr  = Rest tn      -- thirty-second
>
> dhn = 3%4       ; dhnr = Rest dhn     -- dotted half
> dqn = 3%8       ; dqnr = Rest dqn     -- dotted quarter
> den = 3%16      ; denr = Rest den     -- dotted eighth
> dsn = 3%32      ; dsnr = Rest dsn     -- dotted sixteenth

> line, chord :: [Music] -> Music
> line  = foldr (:+:) (Rest 0) 
> chord = foldr (:=:) (Rest 0)

< foldr1           :: (a -> a -> a) -> [a] -> a
< foldr1 f [x]     =  x
< foldr1 f (x:xs)  =  f x (foldr1 f xs)
< foldr1 _ []      =  error "PreludeList.foldr1: empty list"

> cMaj = [ n 4 qn | n <- [c,e,g] ]
>
> cMajArp = line  cMaj
> cMajChd = chord cMaj

> delay :: Dur -> Music -> Music
> delay d m = Rest d :+: m

> repeatM :: Music -> Music
> repeatM m = m :+: repeatM m

> pr1, pr2 :: Pitch -> Music
> pr1 p = Tempo (5%6) 
>           (Tempo (4%3) (mkLn 1 p qn :+:
>                         Tempo (3%2) (mkLn 3 p en :+:
>                                      mkLn 2 p sn :+:
>                                      mkLn 1 p qn    ) :+:
>                         mkLn 1 p qn) :+:
>            Tempo (3%2) (mkLn 6 p en))
>
> pr2 p = Tempo (7%6) 
>           (m1 :+:
>            Tempo (5%4) (mkLn 5 p en) :+:
>            m1 :+:
>            Tempo (3%2) m2)
>   where m1 = Tempo (5%4) (Tempo (3%2) m2 :+: m2)
>         m2 = mkLn 3 p en

> mkLn n p d = line (take n (repeat (Note p d)))

> pr12 :: Music
> pr12 = pr1 (C,5) :=: pr2 (G,5)

> (=:=) :: Dur -> Dur -> Music -> Music
> old =:= new  =  Tempo (new/old)

> dur :: Music -> Dur
>
> dur (Note _ d)    = d
> dur (Rest d)      = d
> dur (m1 :+: m2)   = dur m1   +   dur m2
> dur (m1 :=: m2)   = dur m1 `max` dur m2
> dur (Tempo  a  m) = dur m / a
> dur (Trans  _  m) = dur m
> dur (Instr  _  m) = dur m

> revM :: Music -> Music
>
> revM n@(Note _ _) = n
> revM r@(Rest _)   = r
> revM (Tempo a  m) = Tempo a    (revM m)
> revM (Trans i  m) = Trans i    (revM m)
> revM (Instr i  m) = Instr i    (revM m)
> revM (m1 :+: m2)  = revM m2 :+: revM m1

> revM (m1 :=: m2)
>   = let d1 = dur m1
>         d2 = dur m2
>     in if d1>d2 then revM m1 :=: (Rest (d1-d2) :+: revM m2)
>                 else (Rest (d2-d1) :+: revM m1) :=: revM m2

> cut :: Dur -> Music -> Music
> cut d m | d <= 0  = Rest 0
> cut d (Note x d0) = Note x (min d0 d)
> cut d (Rest d0)   = Rest (min d0 d)
> cut d (m1 :=: m2) = cut d m1 :=: cut d m2
> cut d (Tempo a m) = Tempo a (cut (d*a) m)
> cut d (Trans a m) = Trans a (cut d m)
> cut d (Instr a m) = Instr a (cut d m)
> cut d (m1 :+: m2) = let m1' = cut d m1
>                         m2' = cut (d - dur m1') m2
>                     in m1' :+: m2'

> (/=:) :: Music -> Music -> Music
> m1 /=: m2 = cut (min (dur m1) (dur m2)) (m1 :=: m2)

> trill :: Int -> Dur -> Music -> Music

> trill i d n@(Note p nd)
>   = if d >= nd then n
>     else Note p d
>          :+: trill (negate i) d
>                    (Note (trans i p) (nd-d))
> trill i d (Tempo a m) = Tempo  a (trill i (d*a) m)
> trill i d (Trans a m) = Trans  a (trill i d m)
> trill i d (Instr a m) = Instr  a (trill i d m)
> trill _ _ _           = error "Trill input must be a single note"

> trill'         :: Int -> Dur -> Music -> Music
> trill' i sDur m = trill (negate i) sDur (Trans i m)

> roll :: Dur -> Music -> Music
> roll dur m = trill 0 dur m

> ssfMelody = m1 :+: m2 :+: m3 :+: m4
>
> m1 = trilln 2 5 (bf 6 en) :+:
>      line [ef 7 en, ef 6 en, ef 7 en]
>
> m2 = line [bf 6 sn, c 7 sn, bf 6 sn, g 6 sn, ef 6 en, bf 5 en]
>
> m3 = line [ef 6 sn, f 6 sn, g 6 sn, af 6 sn, bf 6 en, ef 7 en]
>
> m4 = trill 2 tn (bf 6 qn) :+: bf 6 sn :+: denr
>
> ssf = Instr Flute (Tempo 2 (ssfMelody))

> trilln  :: Int -> Int -> Music -> Music
> trilln i nTimes m = trill i (dur m / (nTimes%1)) m

> trilln' :: Int -> Int -> Music -> Music
> trilln' i nTimes m = trilln (negate i) nTimes (Trans i m)

> rolln   :: Int -> Music -> Music
> rolln nTimes m = trilln 0 nTimes m

> data PercussionSound
>   = AcousticBassDrum  -- MIDI Key 35
>   | BassDrum1         -- MIDI Key 36
>   | SideStick         -- ...
>   | AcousticSnare | HandClap      | ElectricSnare | LowFloorTom
>   | ClosedHiHat   | HighFloorTom  | PedalHiHat    | LowTom
>   | OpenHiHat     | LowMidTom     | HiMidTom      | CrashCymbal1
>   | HighTom       | RideCymbal1   | ChineseCymbal | RideBell
>   | Tambourine    | SplashCymbal  | Cowbell       | CrashCymbal2
>   | Vibraslap     | RideCymbal2   | HiBongo       | LowBongo
>   | MuteHiConga   | OpenHiConga   | LowConga      | HighTimbale
>   | LowTimbale    | HighAgogo     | LowAgogo      | Cabasa
>   | Maracas       | ShortWhistle  | LongWhistle   | ShortGuiro
>   | LongGuiro     | Claves        | HiWoodBlock   | LowWoodBlock
>   | MuteCuica     | OpenCuica     | MuteTriangle
>   | OpenTriangle      -- MIDI Key 82
>     deriving (Show,Eq,Ord,Enum)

> perc :: PercussionSound -> Dur -> Music
> perc ps = Note (pitch (fromEnum ps + 35))

> funkGroove
>   = let p1 = perc LowTom        qn
>         p2 = perc AcousticSnare en
>     in Tempo 3 (Instr Percussion (cut 8 (repeatM
>          ( (p1 :+: qnr :+: p2 :+: qnr :+: p2 :+:
>             p1 :+: p1 :+: qnr :+: p2 :+: enr)
>            :=: roll en (perc ClosedHiHat 2) )
>        )))

> rep :: (Music -> Music) -> (Music -> Music) -> Int -> Music -> Music
> rep f g 0 m = Rest 0
> rep f g n m = m :=: g (rep f g (n-1) (f m))

> run       = rep (Trans 5) (delay tn) 8 (c 4 tn)

> cascade   = rep (Trans 4) (delay en) 8 run

> cascades  = rep id (delay sn) 2 cascade

> waterfall = Instr Vibraphone (cascades :+: revM cascades)

> data Cluster = Cluster SNote [Cluster]
> type SNote   = (AbsPitch,Dur)

> selfSim :: [SNote] -> Cluster
> selfSim pat = Cluster (0,0) (map mkCluster pat)
>     where mkCluster note 
>             = Cluster note (map (mkCluster . addmult note) pat)
> 
> addmult (p0,d0) (p1,d1) = (p0+p1,d0*d1)

> fringe :: Int -> Cluster -> [SNote]
> fringe 0 (Cluster note cls) = [note]
> fringe n (Cluster note cls) = concat (map (fringe (n-1)) cls)

< concat :: [[a]] -> [a]
< concat xss = foldr (++) [] xss

> simToHask :: [SNote] -> Music
> simToHask ss = let mkNote (p,d) = Note (pitch p) d
>                in line (map mkNote ss)

> pat :: [SNote]
> pat = [(3,0.5),(4,0.25),(0,0.25),(6,1.0)]

> main 
>  = let s = Trans 60
>             (Tempo 2 
>               (simToHask (fringe 3 (selfSim pat))))
>    in Instr Flute s
>       :=: Instr AcousticBass (Trans (-24) (revM s))

| concat [ concat [ ... ], concat [ ... ], concat [ ... ] ]

