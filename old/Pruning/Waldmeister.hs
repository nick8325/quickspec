{-# LANGUAGE CPP #-}
module QuickSpec.Pruning.Waldmeister where

#include "errors.h"
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Utils
import System.Exit
import System.Process
import System.IO
import Data.Char
import Data.List
import Data.Maybe
import Twee.Base
import qualified Twee.Label as Label

wmUnify :: Int -> [PruningProp] -> PruningProp -> IO Bool
wmUnify timeout bg prop = do
  (exit, std_out, std_err) <-
    readProcessWithExitCode "timeout"
      [show timeout,
       "waldmeister", "--auto", "--noproof", "/dev/stdin"]
      (translate bg prop)

  hPutStr stderr std_err
  case exit of
    ExitSuccess | "Waldmeister states: Goal proved." `elem` lines std_out ->
      return True
    _ ->
      return False

translate :: [PruningProp] -> PruningProp -> String
translate bg prop =
  unlines $
    ["NAME problem",
     "MODE PROOF",
     "SORTS ANY",
     "SIGNATURE"] ++
    [showFun f ++ ": " ++ concat (replicate (arity f) "ANY ") ++ "-> ANY" | f <- fs] ++
    ["ORDERING",
     "KBO",
     intercalate ", " [showFun f ++ "=" ++ show (size f * 100 + 1) | f <- fs],
     intercalate " > " [showFun f | f <- reverse fs]] ++
    ["VARIABLES",
     intercalate ", " [showVar v | v <- vs] ++ ": ANY"] ++
    ["EQUATIONS"] ++
    map showProp bg ++
    ["CONCLUSION"] ++
    [showProp prop]
  where
    fs = map fromFun (usort (funs (prop:bg)))
    vs = usort (vars (prop:bg))
    
    showProp ([] :=>: t :=: u) =
      showTerm t ++ " = " ++ showTerm u
    showTerm (Var x) = showVar x
    showTerm (App f []) = showFun f
    showTerm (App f ts) = showFun f ++ "(" ++ intercalate "," (map showTerm ts) ++ ")"

    showFun Minimal = "minimalConstant"
    showFun (Skolem n) = "sk" ++ show n
    showFun (Function c@Constant{}) = "f" ++ escape (conName c) ++ "_" ++ show (toInt c)
    showFun (Function (Id ty)) = "ty" ++ showTy ty
    showFun (Function (Apply ty)) = "@" ++ showTy ty

    showVar (MkVar n) = "x" ++ show n
    showTy ty = show (Label.label (Ty ty))

    escape = concatMap escape1
    escape1 x
      | isAlphaNum x = [x]
      | otherwise = "_" ++ show (fromEnum x)

instance Label.Labelled Ty where
  cache = tyCache

newtype Ty = Ty Type deriving (Eq, Ord)

{-# NOINLINE tyCache #-}
tyCache :: Label.Cache Ty
tyCache = Label.mkCache
