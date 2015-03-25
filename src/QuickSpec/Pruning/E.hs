{-# LANGUAGE GADTs, CPP #-}
module QuickSpec.Pruning.E where

#ifdef NO_JUKEBOX
eUnify _ _ _ = return False
spassUnify _ _ _ = return False
#else
import QuickSpec.Base
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Utils
import qualified Data.ByteString.Char8 as BS
import Data.Char
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Jukebox.Form as Jukebox
import qualified Jukebox.Name as Jukebox
import qualified Jukebox.Provers.E as Jukebox
import qualified Jukebox.Provers.SPASS as Jukebox
import qualified Jukebox.TPTP.Print as Jukebox
import qualified Text.PrettyPrint as Jukebox

eUnify, spassUnify :: Int -> [PropOf PruningTerm] -> PropOf PruningTerm -> IO Bool
eUnify timeout = foUnify True (Jukebox.runE (Jukebox.EFlags "eprover" (Just timeout) Nothing)) (Left Jukebox.Unsatisfiable)
spassUnify timeout = foUnify False (Jukebox.runSPASS (Jukebox.SPASSFlags "SPASS" (Just timeout) False)) Jukebox.Unsatisfiable

foUnify hasConj prove unsat axioms goal = do
  -- putStrLn ("\nSending to prover: " ++ prettyShow (fmap fromPruningTerm goal))
  let prob = translate hasConj (map unitProp (lhs goal) ++ axioms) (rhs goal)
  --putStrLn (Jukebox.render (Jukebox.prettyProblem "cnf" Jukebox.Normal prob))
  res <- prove prob
  -- print res
  return (res == unsat)

translate :: Bool -> [PropOf PruningTerm] -> Literal PruningTerm ->
             Jukebox.Closed [Jukebox.Input Jukebox.Form]
translate hasConj axioms goal = Jukebox.close_ Jukebox.stdNames $ do
  ty <- Jukebox.newType "i"
  let vs = usort (concatMap vars (unitProp goal:axioms))
      fs = usort (concatMap funs (unitProp goal:axioms))
      ps = usort [ p | p :@: _ <- concatMap literals (unitProp goal:axioms) ]
  varSyms  <- sequence [ Jukebox.newSymbol "X" ty | x <- vs ]
  funSyms  <- sequence [ Jukebox.newFunction (makeFunName x) [] ty | x <- fs]
  propSyms <- sequence [ Jukebox.newFunction (predName x) [] Jukebox.O | x <- ps]
  let var  = find (Map.fromList (zip vs varSyms))
      fun  = find (Map.fromList (zip fs funSyms))
      prop = find (Map.fromList (zip ps propSyms))
      input kind form = Jukebox.Input (BS.pack "clause") kind form
      conj | hasConj = input Jukebox.Conjecture
           | otherwise = input Jukebox.Axiom . Jukebox.nt
  return (conj (translateLiteral var fun prop goal):
          map (input Jukebox.Axiom . translateProp var fun prop) axioms)

makeFunName :: PruningConstant -> String
makeFunName (TermConstant x ty) = conName x
makeFunName (SkolemVariable _)  = "x"
makeFunName (HasType ty)          = "@"

strip = filter (not . isSpace)

find :: (Pretty k, Show v, Ord k) => Map k v -> k -> v
find m x = Map.findWithDefault (error $ "E: couldn't find " ++ prettyShow x ++ " in:\n" ++ showList (Map.toList m)) x m
  where
    showList xs =
      unlines [
        "  " ++ prettyShow k ++ " -> " ++ show v
      | (k, v) <- xs ]

translateProp :: (PruningVariable -> Jukebox.Variable) ->
             (PruningConstant -> Jukebox.Function) ->
             (Predicate -> Jukebox.Function) ->
             PropOf PruningTerm -> Jukebox.Form
translateProp var fun prop p =
  Jukebox.disj
    (translateLiteral var fun prop (rhs p):
     map (Jukebox.nt . translateLiteral var fun prop) (lhs p))

translateLiteral ::
  (PruningVariable -> Jukebox.Variable) ->
  (PruningConstant -> Jukebox.Function) ->
  (Predicate -> Jukebox.Function) ->
  Literal PruningTerm -> Jukebox.Form
translateLiteral var fun prop (t :=: u) =
  Jukebox.Literal (Jukebox.Pos (translateTerm var fun t Jukebox.:=: translateTerm var fun u))
translateLiteral var fun prop (p :@: ts) =
  Jukebox.Literal (Jukebox.Pos (Jukebox.Tru (prop p Jukebox.:@: map (translateTerm var fun) ts)))

translateTerm :: (PruningVariable -> Jukebox.Variable) ->
                 (PruningConstant -> Jukebox.Function) ->
                 PruningTerm -> Jukebox.Term
translateTerm var _fun (Var x) = Jukebox.Var (var x)
translateTerm var  fun (Fun f ts) = fun f Jukebox.:@: map (translateTerm var fun) ts
#endif
