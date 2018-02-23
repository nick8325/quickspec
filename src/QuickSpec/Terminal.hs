{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DefaultSignatures, GADTs #-}
module QuickSpec.Terminal where

import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Test.QuickCheck.Text as Text

class Monad m => MonadTerminal m where
  putLine :: String -> m ()
  putTemp :: String -> m ()

  default putLine :: (MonadTrans t, MonadTerminal m', m ~ t m') => String -> m ()
  putLine = lift . putLine

  default putTemp :: (MonadTrans t, MonadTerminal m', m ~ t m') => String -> m ()
  putTemp = lift . putTemp

instance MonadTerminal m => MonadTerminal (StateT s m)
instance MonadTerminal m => MonadTerminal (ReaderT r m)

putStatus :: MonadTerminal m => String -> m ()
putStatus str = putTemp ("[" ++ str ++ "...]")

clearStatus :: MonadTerminal m => m ()
clearStatus = putTemp ""

withStatus :: MonadTerminal m => String -> m a -> m a
withStatus str mx = putStatus str *> mx <* clearStatus

newtype Terminal a = Terminal (ReaderT Text.Terminal IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTerminal Terminal where
  putLine str = Terminal $ do
    term <- ask
    liftIO $ Text.putLine term str

  putTemp str = Terminal $ do
    term <- ask
    liftIO $ Text.putTemp term str

withNullTerminal :: Terminal a -> IO a
withNullTerminal (Terminal mx) =
  Text.withNullTerminal (runReaderT mx)

withStdioTerminal :: Terminal a -> IO a
withStdioTerminal (Terminal mx) =
  Text.withStdioTerminal (runReaderT mx)
