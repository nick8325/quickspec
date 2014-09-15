{-# LANGUAGE GADTs #-}
module Test.QuickSpec.Pruning.E where

import Test.QuickSpec.Base
import Test.QuickSpec.Term
import Test.QuickSpec.Type
import Test.QuickSpec.Utils
import Test.QuickSpec.Pruning
import System.IO
import System.IO.Unsafe
import Data.List hiding (find)
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.Trans.State.Strict
import qualified Data.ByteString.Char8 as BS
import qualified Jukebox.Form as Jukebox
import qualified Jukebox.Name as Jukebox
import qualified Jukebox.Provers.E as Jukebox
import qualified Jukebox.TPTP.Print as Jukebox
import qualified Jukebox.Toolbox as Jukebox
import qualified Jukebox.Monotonox.ToFOF as Jukebox
import qualified Jukebox.Clausify as Jukebox

newtype EPruner = S [(PruningTerm, PruningTerm)]

instance Pruner EPruner where
  emptyPruner = S []
  unifyUntyped = eUnify
  repUntyped _ = return Nothing

liftIO x = return $! unsafePerformIO x

eUnify :: PruningTerm -> PruningTerm -> State EPruner Bool
eUnify t u = do
  S eqs <- get
  liftIO (putStr ("\nSending to E: " ++ prettyShow (decodeTypes t) ++ " = " ++ prettyShow (decodeTypes u) ++ ": ") >> hFlush stdout)
  let opts = Jukebox.EFlags "eprover" (Just 5) Nothing
      prob = translate eqs t u
  prob' <- liftIO (Jukebox.toFofIO (Jukebox.clausifyIO (Jukebox.ClausifyFlags False)) (Jukebox.tags False) prob)
  res <- liftIO (Jukebox.runE opts prob')
  liftIO (print res)
  case res of
    Left Jukebox.Unsatisfiable ->
      -- Pruned
      return True
    _ -> do
      -- Not pruned
      modify (\(S eqs) -> S ((t,u):eqs))
      return False

translate eqs t u = Jukebox.close_ Jukebox.stdNames $ do
  ty <- Jukebox.newType "i"
  let terms = [t, u] ++ concat [ [l, r] | (l, r) <- eqs ]
      vs = usort (concatMap vars terms)
      fs = usort (concatMap funs terms)
  varSyms <- sequence [ Jukebox.newSymbol (makeVarName x) ty | x <- vs ]
  funSyms <- sequence [ Jukebox.newFunction (makeFunName x) [] ty | x <- fs]
  let var = find (Map.fromList (zip vs varSyms))
      fun = find (Map.fromList (zip fs funSyms))
      input kind form = Jukebox.Input (BS.pack "clause") kind form
  return (input Jukebox.Conjecture (conjecturise (translateEq var fun (t, u))):
          map (input Jukebox.Axiom . translateEq var fun) eqs)

makeVarName (TermVariable x) = 'X':show (varNumber x)
makeVarName (TypeVariable x) = 'A':show (tyVarNumber x)
makeFunName (TermConstant x) = 'f':conName x
makeFunName (TypeConstant x) = 't':show x
makeFunName HasType          = "as"

conjecturise :: Jukebox.Symbolic a => a -> a
conjecturise t =
  case Jukebox.typeOf t of
    Jukebox.Term -> term t
    _ -> Jukebox.recursively conjecturise t
  where
    term (Jukebox.Var (x Jukebox.::: t)) = (x Jukebox.::: Jukebox.FunType [] t) Jukebox.:@: []
    term t = Jukebox.recursively conjecturise t

find m x = Map.findWithDefault (error "E: not found") x m

translateEq var fun (t, u) =
  Jukebox.Literal (Jukebox.Pos (translateTerm var fun t Jukebox.:=: translateTerm var fun u))

translateTerm var fun (Var x) = Jukebox.Var (var x)
translateTerm var fun (Fun f ts) = fun f Jukebox.:@: map (translateTerm var fun) ts

