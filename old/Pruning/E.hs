{-# LANGUAGE GADTs, CPP #-}
module QuickSpec.Pruning.E where

#ifdef NO_JUKEBOX
eUnify _ _ _ = return False
spassUnify _ _ _ = return False
#else
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Utils
import Data.Char
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Jukebox.Form as Jukebox
import qualified Jukebox.Name as Jukebox
import qualified Jukebox.Provers.E as Jukebox
import qualified Jukebox.Provers.SPASS as Jukebox
import qualified Jukebox.TPTP.Print as Jukebox
import qualified Text.PrettyPrint as Jukebox
import Twee.Base

eUnify, spassUnify :: Int -> [PropOf PruningTerm] -> PropOf PruningTerm -> IO Bool
eUnify timeout = foUnify True (Jukebox.runE (Jukebox.EFlags "eprover" (Just timeout) (Just 1000))) (Left Jukebox.Unsatisfiable)
spassUnify timeout = foUnify False (Jukebox.runSPASS (Jukebox.SPASSFlags "SPASS" (Just timeout) False)) Jukebox.Unsatisfiable

foUnify hasConj prove unsat axioms goal = do
  -- putStrLn ("\nSending to prover: " ++ prettyShow (fmap fromPruningTerm goal))
  let prob = translate hasConj (map unitProp (lhs goal) ++ axioms) (rhs goal)
  --putStrLn (Jukebox.render (Jukebox.prettyProblem "cnf" Jukebox.Normal prob))
  res <- prove prob
  -- print res
  return (res == unsat)

translate :: Bool -> [PropOf PruningTerm] -> Literal PruningTerm ->
             Jukebox.Problem Jukebox.Form
translate hasConj axioms goal = Jukebox.runNameM [] $ do
  ty <- Jukebox.newType "i"
  let vs = usort (concatMap vars (unitProp goal:axioms))
      fs = map fromFun (usort (concatMap funs (unitProp goal:axioms)))
      ps = usort [ p | p :@: _ <- concatMap literals (unitProp goal:axioms) ]
  varSyms  <- sequence [ Jukebox.newSymbol "X" ty | x <- vs ]
  funSyms  <- sequence [ Jukebox.newFunction (makeFunName x) [] ty | x <- fs]
  propSyms <- sequence [ Jukebox.newFunction (predName x) [] Jukebox.O | x <- ps]
  let var  = find (Map.fromList (zip vs varSyms))
      fun  = find (Map.fromList (zip fs funSyms))
      prop = find (Map.fromList (zip ps propSyms))
      input kind form = Jukebox.Input "clause" kind Jukebox.Unknown form
      conj | hasConj = input Jukebox.Conjecture
           | otherwise = input (Jukebox.Axiom "axiom") . Jukebox.nt
  return (conj (translateLiteral var fun prop goal):
          map (input (Jukebox.Axiom "axiom") . translateProp var fun prop) axioms)

makeFunName :: PruningConstant -> String
makeFunName Minimal = "a"
makeFunName (Skolem _) = "sk"
makeFunName (Function (Id ty)) = "@"
makeFunName (Function (Apply ty)) = "@"
makeFunName (Function c) = conName c

strip = filter (not . isSpace)

find :: (Pretty k, Show v, Ord k) => Map k v -> k -> v
find m x = Map.findWithDefault (error $ "E: couldn't find " ++ prettyShow x ++ " in:\n" ++ showList (Map.toList m)) x m
  where
    showList xs =
      unlines [
        "  " ++ prettyShow k ++ " -> " ++ show v
      | (k, v) <- xs ]

translateProp :: (Var -> Jukebox.Variable) ->
             (PruningConstant -> Jukebox.Function) ->
             (Predicate -> Jukebox.Function) ->
             PropOf PruningTerm -> Jukebox.Form
translateProp var fun prop p =
  Jukebox.Or
    (translateLiteral var fun prop (rhs p):
     map (Jukebox.nt . translateLiteral var fun prop) (lhs p))

translateLiteral ::
  (Var -> Jukebox.Variable) ->
  (PruningConstant -> Jukebox.Function) ->
  (Predicate -> Jukebox.Function) ->
  Literal PruningTerm -> Jukebox.Form
translateLiteral var fun prop (t :=: u) =
  Jukebox.Literal (Jukebox.Pos (translateTerm var fun t Jukebox.:=: translateTerm var fun u))
translateLiteral var fun prop (p :@: ts) =
  Jukebox.Literal (Jukebox.Pos (Jukebox.Tru (prop p Jukebox.:@: map (translateTerm var fun) ts)))

translateTerm :: (Var -> Jukebox.Variable) ->
                 (PruningConstant -> Jukebox.Function) ->
                 PruningTerm -> Jukebox.Term
translateTerm var _fun (Var x) = Jukebox.Var (var x)
translateTerm var  fun (App f ts) = fun f Jukebox.:@: map (translateTerm var fun) ts
#endif
