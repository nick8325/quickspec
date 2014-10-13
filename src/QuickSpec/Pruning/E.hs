{-# LANGUAGE GADTs #-}
module QuickSpec.Pruning.E where

import QuickSpec.Base
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
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

eUnify :: [(PruningTerm, PruningTerm)] -> PruningTerm -> PruningTerm -> IO Bool
eUnify eqs t u = do
  --eliftIO (putStr ("\nSending to E: " ++ prettyShow (fromPruningTerm t) ++ " = " ++ prettyShow (fromPruningTerm u) ++ ": ") >> hFlush stdout)
  let opts = Jukebox.EFlags "eprover" (Just 1) Nothing
      prob = translate eqs t u
  putStrLn (Jukebox.render (Jukebox.prettyProblem "fof" Jukebox.Normal prob))
  res <- Jukebox.runE opts prob
  --eliftIO (print res)
  case res of
    Left Jukebox.Unsatisfiable ->
      -- Pruned
      return True
    _ -> do
      return False

translate :: [(PruningTerm, PruningTerm)] -> PruningTerm -> PruningTerm ->
             Jukebox.Closed [Jukebox.Input Jukebox.Form]
translate eqs t u = Jukebox.close_ Jukebox.stdNames $ do
  ty <- Jukebox.newType "i"
  let terms = [skolemise t, skolemise u] ++ concat [ [l, r] | (l, r) <- eqs ]
      vs = usort (concatMap vars terms)
      fs = usort (concatMap funs terms)
  varSyms <- sequence [ Jukebox.newSymbol "X" ty | x <- vs ]
  funSyms <- sequence [ Jukebox.newFunction (makeFunName x) [] ty | x <- fs]
  let var = find (Map.fromList (zip vs varSyms))
      fun = find (Map.fromList (zip fs funSyms))
      input kind form = Jukebox.Input (BS.pack "clause") kind form
  return (input Jukebox.Conjecture (conjecturise (translateEq var fun (skolemise t, skolemise u))):
          map (input Jukebox.Axiom . translateEq var fun) eqs)

makeFunName :: PruningConstant -> String
makeFunName (TermConstant x n ty) = conName x
makeFunName (HasType ty)          = "@"

strip = filter (not . isSpace)

conjecturise :: Jukebox.Symbolic a => a -> a
conjecturise t =
  case Jukebox.typeOf t of
    Jukebox.Term -> term t
    _ -> Jukebox.recursively conjecturise t
  where
    term (Jukebox.Var (x Jukebox.::: t)) = (x Jukebox.::: Jukebox.FunType [] t) Jukebox.:@: []
    term t = Jukebox.recursively conjecturise t

skolemise :: PruningTerm -> PruningTerm
skolemise (Fun f xs) = Fun f (map skolemise xs)
skolemise x@(Var (TermVariable _ ty)) = Fun (HasType ty) [x]

find :: (Pretty k, Show v, Ord k) => Map k v -> k -> v
find m x = Map.findWithDefault (error $ "E: couldn't find " ++ prettyShow x ++ " in:\n" ++ showList (Map.toList m)) x m
  where
    showList xs =
      unlines [
        "  " ++ prettyShow k ++ " -> " ++ show v
      | (k, v) <- xs ]

translateEq :: (PruningVariable -> Jukebox.Variable) ->
               (PruningConstant -> Jukebox.Function) ->
               (PruningTerm, PruningTerm) -> Jukebox.Form
translateEq var fun (t, u) =
  Jukebox.Literal (Jukebox.Pos (translateTerm var fun t Jukebox.:=: translateTerm var fun u))

translateTerm :: (PruningVariable -> Jukebox.Variable) ->
                 (PruningConstant -> Jukebox.Function) ->
                 PruningTerm -> Jukebox.Term
translateTerm var _fun (Var x) = Jukebox.Var (var x)
translateTerm var  fun (Fun f ts) = fun f Jukebox.:@: map (translateTerm var fun) ts

