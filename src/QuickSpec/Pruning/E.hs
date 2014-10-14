{-# LANGUAGE GADTs #-}
module QuickSpec.Pruning.E where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.Prop
import QuickSpec.Pruning
import System.IO
import System.IO.Unsafe
import Control.Monad.Trans.State.Strict
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as BS
import qualified Jukebox.Form as Jukebox
import qualified Jukebox.Name as Jukebox
import qualified Jukebox.Provers.E as Jukebox
import qualified Jukebox.Toolbox as Jukebox
import qualified Jukebox.Monotonox.ToFOF as Jukebox
import qualified Jukebox.Clausify as Jukebox
import qualified Jukebox.TPTP.Print as Jukebox
import qualified Text.PrettyPrint.HughesPJ as Jukebox
import Data.Char

eUnify :: [PropOf PruningTerm] -> PropOf PruningTerm -> IO Bool
eUnify axioms goal = do
  -- putStrLn ("\nSending to E: " ++ prettyShow (fmap fromPruningTerm goal))
  let opts = Jukebox.EFlags "eprover" (Just 0) Nothing
      prob = translate (map unitProp (lhs goal) ++ axioms) (rhs goal)
  -- putStrLn (Jukebox.render (Jukebox.prettyProblem "fof" Jukebox.Normal prob))
  res <- Jukebox.runE opts prob
  --eliftIO (print res)
  case res of
    Left Jukebox.Unsatisfiable ->
      -- Pruned
      return True
    _ -> do
      return False

translate :: [PropOf PruningTerm] -> Literal PruningTerm ->
             Jukebox.Closed [Jukebox.Input Jukebox.Form]
translate axioms goal = Jukebox.close_ Jukebox.stdNames $ do
  ty <- Jukebox.newType "i"
  let terms = usort (concatMap propTerms (unitProp goal:axioms))
      vs = usort (concatMap vars terms)
      fs = usort (concatMap funs terms)
      ps = usort [ p | p :@: _ <- concatMap propLiterals (unitProp goal:axioms) ]
  varSyms  <- sequence [ Jukebox.newSymbol "X" ty | x <- vs ]
  funSyms  <- sequence [ Jukebox.newFunction (makeFunName x) [] ty | x <- fs]
  propSyms <- sequence [ Jukebox.newFunction (predName x) [] Jukebox.O | x <- ps]
  let var  = find (Map.fromList (zip vs varSyms))
      fun  = find (Map.fromList (zip fs funSyms))
      prop = find (Map.fromList (zip ps propSyms))
      input form = Jukebox.Input (BS.pack "clause") Jukebox.Axiom form
  return (input (Jukebox.nt (translateLiteral var fun prop goal)):
          map (input . translateProp var fun prop) axioms)

makeFunName :: PruningConstant -> String
makeFunName (TermConstant x n ty) = conName x
makeFunName (SkolemVariable _)    = "x"
makeFunName (HasType ty)          = "@"

strip = filter (not . isSpace)

find :: (Pretty k, Show v, Ord k) => Map k v -> k -> v
find m x = Map.findWithDefault (error $ "E: couldn't find " ++ prettyShow x ++ " in:\n" ++ showList (Map.toList m)) x m
  where
    showList xs =
      unlines [
        "  " ++ prettyShow k ++ " -> " ++ show v
      | (k, v) <- xs ]

translateProp :: (Int -> Jukebox.Variable) ->
             (PruningConstant -> Jukebox.Function) ->
             (Predicate -> Jukebox.Function) ->
             PropOf PruningTerm -> Jukebox.Form
translateProp var fun prop p =
  Jukebox.disj
    (translateLiteral var fun prop (rhs p):
     map (Jukebox.nt . translateLiteral var fun prop) (lhs p))

translateLiteral ::
  (Int -> Jukebox.Variable) ->
  (PruningConstant -> Jukebox.Function) ->
  (Predicate -> Jukebox.Function) ->
  Literal PruningTerm -> Jukebox.Form
translateLiteral var fun prop (t :=: u) =
  Jukebox.Literal (Jukebox.Pos (translateTerm var fun t Jukebox.:=: translateTerm var fun u))
translateLiteral var fun prop (p :@: ts) =
  Jukebox.Literal (Jukebox.Pos (Jukebox.Tru (prop p Jukebox.:@: map (translateTerm var fun) ts)))

translateTerm :: (Int -> Jukebox.Variable) ->
                 (PruningConstant -> Jukebox.Function) ->
                 PruningTerm -> Jukebox.Term
translateTerm var _fun (Var x) = Jukebox.Var (var x)
translateTerm var  fun (Fun f ts) = fun f Jukebox.:@: map (translateTerm var fun) ts

