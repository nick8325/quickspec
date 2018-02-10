{-# LANGUAGE DeriveGeneric, TypeFamilies, DeriveFunctor, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, FlexibleContexts #-}
module QuickSpec.Prop where

import Control.Monad
import qualified Data.DList as DList
import Data.Ord
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.Term
import GHC.Generics
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.Trans.State.Strict
import Text.PrettyPrint

data Prop a =
  (:=>:) {
    lhs :: [Equation a],
    rhs :: Equation a }
  deriving (Show, Generic, Functor)

instance Symbolic f a => Symbolic f (Prop a) where
  termsDL (lhs :=>: rhs) =
    termsDL lhs `mplus` termsDL rhs
  subst sub (lhs :=>: rhs) =
    subst sub lhs :=>: subst sub rhs

instance Ord a => Eq (Prop a) where
  x == y = x `compare` y == EQ
instance Ord a => Ord (Prop a) where
  compare = comparing (\p -> (usort (lhs p), rhs p))

infix 4 :=>:

literals :: Prop a -> [Equation a]
literals p = rhs p:lhs p

unitProp :: Equation a -> Prop a
unitProp p = [] :=>: p

mapFun :: (fun1 -> fun2) -> Prop (Term fun1) -> Prop (Term fun2)
mapFun f = fmap (fmap f)

instance Typed a => Typed (Prop a) where
  typ _ = typeOf True
  otherTypesDL p = DList.fromList (literals p) >>= typesDL
  typeSubst_ sub (lhs :=>: rhs) =
    map (typeSubst_ sub) lhs :=>: typeSubst_ sub rhs

instance Pretty a => Pretty (Prop a) where
  pPrint ([] :=>: rhs) = pPrint rhs
  pPrint p =
    hsep (punctuate (text " &") (map pPrint (lhs p))) <+> text "=>" <+> pPrint (rhs p)

data Equation a = a :=: a deriving (Show, Eq, Ord, Generic, Functor)

instance Symbolic f a => Symbolic f (Equation a) where
  termsDL (t :=: u) = termsDL t `mplus` termsDL u
  subst sub (t :=: u) = subst sub t :=: subst sub u

infix 5 :=:

instance Typed a => Typed (Equation a) where
  typ (t :=: _) = typ t
  otherTypesDL (t :=: u) = otherTypesDL t `mplus` typesDL u
  typeSubst_ sub (x :=: y) = typeSubst_ sub x :=: typeSubst_ sub y

instance Pretty a => Pretty (Equation a) where
  pPrintPrec _ _ (x :=: y) = pPrint x <+> text "=" <+> pPrint y

infix 4 ===
(===) :: a -> a -> Prop a
x === y = [] :=>: x :=: y

----------------------------------------------------------------------
-- Making properties look pretty (naming variables, etc.)
----------------------------------------------------------------------

class PrettyArity fun where
  prettyArity :: fun -> Int
  prettyArity _ = 0

prettyProp ::
  (Typed fun, Apply (Term fun), PrettyTerm fun, PrettyArity fun) =>
  (Type -> [String]) -> Prop (Term fun) -> Doc
prettyProp cands =
  pPrint . nameVars cands . eta . canonicalise
  where
    eta prop =
      case filter isPretty (etaExpand prop) of
        [] -> last (etaExpand prop)
        (prop:_) -> prop

    isPretty (_ :=>: t :=: u) = isPretty1 t && isPretty1 u
    isPretty1 (App f ts) = prettyArity f <= length ts
    isPretty1 (Var _) = True

    etaExpand prop@(lhs :=>: t :=: u) =
      prop:
      case (tryApply t x, tryApply u x) of
        (Just t', Just u') -> etaExpand (lhs :=>: t' :=: u')
        _ -> []
      where
        x = Var (V (head (typeArgs (typ t))) n)
        n = maximum (0:map (succ . var_id) (vars prop))

data Named fun = Name String | Fun fun
instance Pretty fun => Pretty (Named fun) where
  pPrintPrec l p (Name name) = text name
  pPrintPrec l p (Fun fun) = pPrintPrec l p fun
instance PrettyTerm fun => PrettyTerm (Named fun) where
  termStyle Name{} = uncurried
  termStyle (Fun fun) = termStyle fun

nameVars :: (Type -> [String]) -> Prop (Term fun) -> Prop (Term (Named fun))
nameVars cands p =
  subst (\x -> Map.findWithDefault undefined x sub) (fmap (fmap Fun) p)
  where
    sub = Map.fromList (evalState (mapM assign (usort (vars p))) Set.empty)
    assign x = do
      s <- get
      let names = supply (cands (typ x))
          name = head (filter (`Set.notMember` s) names)
      modify (Set.insert name)
      return (x, App (Name name) [])
