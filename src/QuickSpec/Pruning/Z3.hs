module QuickSpec.Pruning.Z3 where

import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Utils
import QuickSpec.Term
import QuickSpec.Base
import Z3.Monad hiding (Symbol, Context, reset)
import Z3.Opts

z3Unify :: [PropOf PruningTerm] -> PropOf PruningTerm -> IO Bool
z3Unify axioms goal =
  evalZ3With Nothing (opt "SOFT_TIMEOUT" (500 :: Int)) $ do
    bool <- mkBoolSort
    ind  <- mkStringSymbol "$i" >>= mkUninterpretedSort
    sequence_ [ flatten bool ind prop >>= assertCnstr | prop <- axioms ]
    flatten bool ind goal >>= mkNot >>= assertCnstr
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
  quantify ind (usort (concatMap vars (propTerms (lhs :=>: rhs)))) res

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

flattenTerm ind (Fun f ts) = flattenApp ind ind f ts

quantify ind [] t = return t
quantify ind xs t = do
  apps <- mapM (flattenTerm ind . Var) xs >>= mapM toApp
  mkForallConst [] apps t
