{-# LANGUAGE CPP #-}
module QuickSpec.Pruning.Waldmeister where

#include "errors.h"
import QuickSpec.Base
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Utils
import System.Exit
import System.Process
import System.IO
import Data.Char
import Data.List
import Data.Maybe

wmUnify :: Int -> [PropOf PruningTerm] -> PropOf PruningTerm -> IO Bool
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

translate :: [PropOf PruningTerm] -> PropOf PruningTerm -> String
translate bg prop =
  unlines $
    ["NAME problem",
     "MODE PROOF",
     "SORTS ANY",
     "SIGNATURE"] ++
    [showFun f ++ ": " ++ concat (replicate (funArity f) "ANY ") ++ "-> ANY" | f <- fs] ++
    ["ORDERING",
     "KBO",
     intercalate ", " [showFun f ++ "=" ++ show (truncate (funSize f) * 100 + 1) | f <- fs],
     intercalate " > " [showFun f | f <- reverse fs]] ++
    ["VARIABLES",
     intercalate ", " [showVar v | v <- vs] ++ ": ANY"] ++
    ["EQUATIONS"] ++
    map showProp bg ++
    ["CONCLUSION"] ++
    [showProp prop]
  where
    unisorted = length (usort ([ ty | HasType ty <- funs (prop:bg) ])) == 1
    relevant HasType{} | unisorted = False
    relevant _ = True
    fs = filter relevant (usort (funs (prop:bg)))
    vs = usort (vars (prop:bg))
    tys = usort $ [ ty | TermConstant _ ty <- fs ] ++ [ ty | HasType ty <- fs ]
    
    showProp ([] :=>: t :=: u) =
      showTerm t ++ " = " ++ showTerm u
    showTerm (Var x) = showVar x
    showTerm (Fun f []) = showFun f
    showTerm (Fun HasType{} [t]) | unisorted = showTerm t
    showTerm (Fun f ts) = showFun f ++ "(" ++ intercalate "," (map showTerm ts) ++ ")"

    showFun (SkolemVariable (PruningVariable n)) = "sk" ++ show n
    showFun (TermConstant c ty) = "f" ++ escape (conName c) ++ "_" ++ show (conIndex c) ++ "_" ++ showTy ty
    showFun (HasType ty) = "ty" ++ showTy ty

    showVar (PruningVariable n) = "x" ++ show n
    showTy ty = show (fromMaybe __ (elemIndex ty tys))

    escape = concatMap escape1
    escape1 x
      | isAlphaNum x = [x]
      | otherwise = "_" ++ show (fromEnum x)
