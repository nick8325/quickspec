{-# LANGUAGE CPP #-}
module QuickSpec.Pruning.Z3 where

#ifdef NO_Z3
z3Unify _ _ _ = return False
#else
import QuickSpec.Prop
import QuickSpec.Pruning
import QuickSpec.Utils
import Z3.Monad hiding (Symbol, Context, reset)
import Twee.Base

z3Unify :: Int -> [PruningProp] -> PruningProp -> IO Bool
z3Unify timeout axioms goal =
  evalZ3With Nothing (opt "SOFT_TIMEOUT" timeout) $ do
    bool <- mkBoolSort
    ind  <- mkStringSymbol "$i" >>= mkUninterpretedSort
    sequence_ [ flatten bool ind prop >>= solverAssertCnstr | prop <- axioms ]
    flatten bool ind goal >>= mkNot >>= solverAssertCnstr
    res <- check
    case res of
      Unsat ->
        return True
      _ ->
        return False

flatten :: Sort -> Sort -> PropOf PruningTerm -> Z3 AST
flatten bool ind (lhs :=>: rhs) = do
  lhs' <- mapM (flattenLit bool ind) lhs >>= mkAnd'
  rhs' <- flattenLit bool ind rhs
  res <- mkImplies lhs' rhs'
  quantify ind (usort (vars (lhs :=>: rhs))) res

mkAnd' [] = mkTrue
mkAnd' [x] = return x
mkAnd' xs = mkAnd xs

flattenLit :: Sort -> Sort -> Literal PruningTerm -> Z3 AST
flattenLit bool ind (p :@: ts) = flattenApp bool ind p ts
flattenLit bool ind (t :=: u) = do
  t' <- flattenTerm ind t
  u' <- flattenTerm ind u
  mkEq t' u'

flattenApp :: Show a => Sort -> Sort -> a -> [PruningTerm] -> Z3 AST
flattenApp res ind f ts = do
  sym <- mkStringSymbol (show f)
  f'  <- mkFuncDecl sym (replicate (length ts) ind) res
  args <- mapM (flattenTerm ind) ts
  mkApp f' args

flattenTerm :: Sort -> PruningTerm -> Z3 AST
flattenTerm ind (Var x) = do
  sym <- mkStringSymbol (show x)
  mkConst sym ind

flattenTerm ind (App f ts) = flattenApp ind ind f ts

quantify ind [] t = return t
quantify ind xs t = do
  apps <- mapM (flattenTerm ind . build . var) xs >>= mapM toApp
  mkForallConst [] apps t
#endif
