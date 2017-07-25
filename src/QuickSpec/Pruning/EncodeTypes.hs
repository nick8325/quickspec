-- Encode monomorphic types during pruning.
{-# LANGUAGE TypeFamilies, RecordWildCards, FlexibleInstances #-}
module QuickSpec.Pruning.EncodeTypes where

import QuickSpec.Pruning
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Prop
import qualified Data.Set as Set
import Data.Set(Set)
import Data.List
import Data.Proxy

data Tagged f =
    Func f
  | Tag Type
  deriving (Eq, Ord, Show, Typeable)

instance Arity f => Arity (Tagged f) where
  arity (Func f) = arity f
  arity (Tag _) = 1

instance Sized f => Sized (Tagged f) where
  size (Func f) = size f
  size (Tag _) = 0

instance Pretty f => Pretty (Tagged f) where
  pPrint (Func f) = pPrint f
  pPrint (Tag ty) = pPrint ty

instance PrettyTerm f => PrettyTerm (Tagged f) where
  termStyle (Func f) = termStyle f
  termStyle (Tag _) = uncurried

type TypedTerm f = Term f
type UntypedTerm f = Term (Tagged f)

data State f =
  State {
    st_pruner :: Pruner (UntypedTerm f),
    st_functions :: Set (Tagged f) }

encodeMonoTypes :: (Ord f, Typed f, Arity f) =>
  Pruner (UntypedTerm f) -> Pruner (TypedTerm f)
encodeMonoTypes pruner =
  makePruner normaliseMono addMono
    State {
      st_pruner = pruner,
      st_functions = Set.empty }

normaliseMono :: (Ord f, Typed f) =>
  State f -> TypedTerm f -> TypedTerm f
normaliseMono State{..} =
  -- Note that we don't call addFunction on the functions in the term.
  -- This is because doing so might be expensive, as adding typing
  -- axioms starts the completion algorithm.
  -- This is OK because in encode, we tag all functions and variables
  -- with their types (i.e. we can fall back to the naive type encoding).
  decode . normalise st_pruner . encode

addMono :: (Ord f, Typed f, Arity f) =>
  Prop (TypedTerm f) -> State f -> State f
addMono prop state =
  State{
    st_pruner = add st_pruner (fmap encode prop),
    st_functions = st_functions }
  where
    State{..} =
      foldl' addFunction state (funs prop)

addFunction :: (Ord f, Typed f, Arity f) =>
  State f -> f -> State f
addFunction st@State{..} f
  | Func f `Set.member` st_functions = st
  | otherwise =
    State{
      st_pruner = foldl' add st_pruner (concatMap typingAxioms funcs),
      st_functions = Set.union st_functions (Set.fromList funcs) }
    where
      funcs = Func f:tags
      tags =
        Set.toList $
          Set.fromList (map Tag (typeRes (typ f):typeArgs (typ f)))
          Set.\\ st_functions

-- Compute the typing axioms for a function or type tag.
typingAxioms :: (Ord f, Typed f, Arity f) =>
  Tagged f -> [Prop (UntypedTerm f)]
typingAxioms (Tag ty) =
  [tag ty (tag ty x) === tag ty x]
  where
    x = Var (V ty 0)
typingAxioms (Func func) =
  [tag res t === t] ++
  [tagArg i ty === t | (i, ty) <- zip [0..] args]
  where
    f = Func func
    xs = take n (map (Var . V typeVar) [0..])

    ty = typ func
    -- Use arity rather than typeArity, so that we can support
    -- partially-applied functions
    n = arity func
    args = take n (typeArgs ty)
    res = typeDrop n ty

    t = App f xs

    tagArg i ty =
      App f $
        take i xs ++
        [tag ty (xs !! i)] ++
        drop (i+1) xs

tag :: Type -> UntypedTerm f -> UntypedTerm f
tag ty t = App (Tag ty) [t]

encode :: Typed f => TypedTerm f -> UntypedTerm f
-- We always add type tags; see comment in normaliseMono.
-- In the common case, twee will immediately remove these surplus type tags
-- by rewriting using the typing axioms.
encode (Var x) = tag (typ x) (Var x)
encode (App f ts) =
  tag (typeRes (typ f)) (App (Func f) (map encode ts))

decode :: Typed f => UntypedTerm f -> TypedTerm f
decode = dec Nothing
  where
    dec _ (App (Tag ty) [t]) =
      dec (Just ty) t
    dec _ (App Tag{} _) =
      error "Tag function applied with wrong arity"
    dec (Just ty) (Var (V _ x)) =
      Var (V ty x)
    dec Nothing (Var _) =
      error "Naked variable in type-encoded term"
    dec _ (App (Func f) ts) =
      App f $
        zipWith dec
          (map Just (typeArgs (typ f)))
          ts
