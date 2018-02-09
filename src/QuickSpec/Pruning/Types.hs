-- Encode monomorphic types during pruning.
{-# LANGUAGE RecordWildCards, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
module QuickSpec.Pruning.Types where

import QuickSpec.Pruning
import qualified QuickSpec.Pruning.Background as Background
import QuickSpec.Pruning.Background(Background)
import QuickSpec.Testing
import QuickSpec.Term
import QuickSpec.Type
import QuickSpec.Prop
import Control.Monad.IO.Class
import Control.Monad.Trans.Class

data Tagged fun =
    Func fun
  | Tag Type
  deriving (Eq, Ord, Show, Typeable)

instance Arity fun => Arity (Tagged fun) where
  arity (Func f) = arity f
  arity (Tag _) = 1

instance Sized fun => Sized (Tagged fun) where
  size (Func f) = size f
  size (Tag _) = 0

instance Pretty fun => Pretty (Tagged fun) where
  pPrint (Func f) = pPrint f
  pPrint (Tag ty) = pPrint ty

instance PrettyTerm fun => PrettyTerm (Tagged fun) where
  termStyle (Func f) = termStyle f
  termStyle (Tag _) = uncurried

instance EqualsBonus (Tagged fun) where

type TypedTerm fun = Term fun
type UntypedTerm fun = Term (Tagged fun)

newtype Pruner fun pruner a =
  Pruner { run :: pruner a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term)

instance MonadTrans (Pruner fun) where
  lift = Pruner

instance (Ord fun, Typed fun, Arity fun, MonadPruner (UntypedTerm fun) pruner) => MonadPruner (TypedTerm fun) (Pruner fun pruner) where
  normaliser =
    Pruner $ do
      norm <- normaliser :: pruner (UntypedTerm fun -> UntypedTerm fun)
      
      -- Note that we don't call addFunction on the functions in the term.
      -- This is because doing so might be expensive, as adding typing
      -- axioms starts the completion algorithm.
      -- This is OK because in encode, we tag all functions and variables
      -- with their types (i.e. we can fall back to the naive type encoding).
      return $ \t ->
        decode . norm . encode $ t

  add prop = lift (add (encode <$> prop))

instance (Ord fun, Typed fun, Arity fun) => Background (Tagged fun) where
  background = typingAxioms

-- Compute the typing axioms for a function or type tag.
typingAxioms :: (Ord fun, Typed fun, Arity fun) =>
  Tagged fun -> [Prop (UntypedTerm fun)]
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

tag :: Type -> UntypedTerm fun -> UntypedTerm fun
tag ty t = App (Tag ty) [t]

encode :: Typed fun => TypedTerm fun -> UntypedTerm fun
-- We always add type tags; see comment in normaliseMono.
-- In the common case, twee will immediately remove these surplus type tags
-- by rewriting using the typing axioms.
encode (Var x) = tag (typ x) (Var x)
encode (App f ts) =
  tag (typeRes (typ f)) (App (Func f) (map encode ts))

decode :: Typed fun => UntypedTerm fun -> TypedTerm fun
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
