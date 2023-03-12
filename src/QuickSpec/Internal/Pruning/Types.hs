-- Encode monomorphic types during pruning.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
module QuickSpec.Internal.Pruning.Types where

import QuickSpec.Internal.Pruning
import QuickSpec.Internal.Pruning.Background(Background(..))
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Term
import QuickSpec.Internal.Type
import QuickSpec.Internal.Prop hiding (mapFun)
import QuickSpec.Internal.Terminal
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Maybe

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
  pPrint (Tag ty) = text "tag[" <#> pPrint ty <#> text "]"

instance PrettyTerm fun => PrettyTerm (Tagged fun) where
  termStyle (Func f) = termStyle f
  termStyle (Tag _) = uncurried

instance Typed fun => Typed (Tagged fun) where
  typ (Func f) = typ f
  typ (Tag ty) = arrowType [ty] ty

  typeSubst_ sub (Func f) = Func (typeSubst_ sub f)
  typeSubst_ sub (Tag ty) = Tag (typeSubst_ sub ty)

instance EqualsBonus (Tagged fun) where

type TypedTerm fun = Term fun
type UntypedTerm fun = Term (Tagged fun)

newtype Pruner fun pruner a =
  Pruner { run :: pruner a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTester testcase term, MonadTerminal)

instance MonadTrans (Pruner fun) where
  lift = Pruner

instance (PrettyTerm fun, Typed fun, MonadPruner (UntypedTerm fun) norm pruner) => MonadPruner (TypedTerm fun) norm (Pruner fun pruner) where
  normaliser =
    Pruner $ do
      norm <- normaliser :: pruner (UntypedTerm fun -> norm)

      -- Note that we don't call addFunction on the functions in the term.
      -- This is because doing so might be expensive, as adding typing
      -- axioms starts the completion algorithm.
      -- This is OK because in encode, we tag all functions and variables
      -- with their types (i.e. we can fall back to the naive type encoding).
      return $ \t ->
        norm . encode $ t

  add prop = lift (add (encode <$> canonicalise prop))

  decodeNormalForm hole t =
    Pruner $ do
      t <- decodeNormalForm (fmap (fmap Func) . hole) t
      let f (Func x) = NotId x
          f (Tag _) = Id
      return $ t >>= eliminateId . mapFun f

instance (Typed fun, Arity fun, Background fun) => Background (Tagged fun) where
  background = typingAxioms

-- Compute the typing axioms for a function or type tag.
typingAxioms :: (Typed fun, Arity fun, Background fun) =>
  Tagged fun -> [Prop (UntypedTerm fun)]
typingAxioms (Tag ty) =
  [tag ty (tag ty x) === tag ty x]
  where
    x = Var (V ty 0)
typingAxioms (Func func) =
  [tag res t === t] ++
  [tagArg i ty === t | (i, ty) <- zip [0..] args] ++
  map (fmap encode) (background func)
  where
    f = Fun (Func func)
    xs = take n (map (Var . V typeVar) [0..])

    ty = typ func
    -- Use arity rather than typeArity, so that we can support
    -- partially-applied functions
    n = arity func
    args = take n (typeArgs ty)
    res = typeDrop n ty

    t = f :@: xs

    tagArg i ty =
      f :@:
        (take i xs ++
         [tag ty (xs !! i)] ++
         drop (i+1) xs)

tag :: Type -> UntypedTerm fun -> UntypedTerm fun
tag ty t = Fun (Tag ty) :$: t

encode :: Typed fun => TypedTerm fun -> UntypedTerm fun
-- We always add type tags; see comment in normaliseMono.
-- In the common case, twee will immediately remove these surplus type tags
-- by rewriting using the typing axioms.
encode (Var x) = tag (typ x) (Var x)
encode (Fun f :@: ts) =
  tag (typeDrop (length ts) (typ f)) (Fun (Func f) :@: map encode ts)
encode _ = error "partial application"
