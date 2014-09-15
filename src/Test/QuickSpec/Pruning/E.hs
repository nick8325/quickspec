{-# LANGUAGE GADTs #-}
module Test.QuickSpec.Reasoning.E where

import Test.QuickSpec.Term hiding (sym)
import Test.QuickSpec.Equation
import Test.QuickSpec.Utils
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.Typeable
import System.IO
import System.IO.Unsafe
import Data.List hiding (find)
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.State
import qualified Data.ByteString.Char8 as BS
import qualified Jukebox.Form as Jukebox
import qualified Jukebox.Name as Jukebox
import qualified Jukebox.Provers.E as Jukebox
import qualified Jukebox.TPTP.Print as Jukebox
import qualified Jukebox.Toolbox as Jukebox
import qualified Jukebox.Monotonox.ToFOF as Jukebox
import qualified Jukebox.Clausify as Jukebox

type Context = ()
type EQ = StateT [Equation] IO

initial :: Int -> [Symbol] -> [Tagged Term] -> Context
initial _ _ _ = ()

evalEQ :: Context -> EQ a -> a
evalEQ ctx x = unsafePerformIO (evalStateT x [])

unify :: Equation -> EQ Bool
unify eq = do
  eqs <- get
  liftIO (putStr (show eq ++ ": ") >> hFlush stdout)
  let opts = Jukebox.EFlags "eprover" (Just 5) Nothing
      prob = translate eqs eq
  prob' <- liftIO (Jukebox.toFofIO (Jukebox.clausifyIO (Jukebox.ClausifyFlags False)) (Jukebox.tags False) prob)
  res <- liftIO (Jukebox.runE opts prob')
  liftIO (print res)
  case res of
    Left Jukebox.Unsatisfiable ->
      -- Pruned
      return True
    _ -> do
      -- Not pruned
      modify (eq:)
      return False

translate eqs eq = Jukebox.close_ Jukebox.stdNames $ do
  let vars = nub (concatMap eqVars (eq:eqs))
      funs = nub (concatMap eqFuns (eq:eqs))
      tys = nub (concat [res:args | sym <- vars ++ funs, let (args, res) = symbolTypes sym])
  tyNames <- mapM Jukebox.newType (map show tys)
  let ty = find (Map.fromList (zip tys tyNames))
  varSyms <- sequence [ Jukebox.newSymbol ('V':name x) (ty (symbolType x)) | x <- vars ]
  funSyms <- sequence [ Jukebox.newFunction (name x) (map ty args) (ty res) | x <- funs, let (args, res) = symbolTypes x ]
  let var = find (Map.fromList (zip vars varSyms))
      fun = find (Map.fromList (zip funs funSyms))
      input kind form = Jukebox.Input (BS.pack "clause") kind form
  return (input Jukebox.Conjecture (conjecturise (translateEq ty var fun eq)):
          map (input Jukebox.Axiom . translateEq ty var fun) eqs)

conjecturise :: Jukebox.Symbolic a => a -> a
conjecturise t =
  case Jukebox.typeOf t of
    Jukebox.Term -> term t
    _ -> Jukebox.recursively conjecturise t
  where
    term (Jukebox.Var (x Jukebox.::: t)) = (x Jukebox.::: Jukebox.FunType [] t) Jukebox.:@: []
    term t = Jukebox.recursively conjecturise t

find m x = Map.findWithDefault (error "E: not found") x m
eqVars (t :=: u) = vars t ++ vars u
eqFuns (t :=: u) = funs t ++ funs u

translateEq ty var fun (t :=: u) =
  Jukebox.Literal (Jukebox.Pos (translateTerm ty var fun t Jukebox.:=: translateTerm ty var fun u))

translateTerm ty var fun (Var x) = Jukebox.Var (var x)
translateTerm ty var fun (Const x) = fun x Jukebox.:@: []
translateTerm ty var fun (App t u) = f Jukebox.:@: (xs ++ [translateTerm ty var fun u])
  where
    f Jukebox.:@: xs = translateTerm ty var fun t

symbolTypes :: Symbol -> ([TypeRep], TypeRep)
symbolTypes s = loop (symbolArity s) (symbolType s)
  where
    loop 0 ty = ([], ty)
    loop n ty = (x:xs, ys)
      where
        Just (x, ty') = splitArrow ty
        (xs, ys) = loop (n-1) ty'
