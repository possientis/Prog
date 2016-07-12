{-# LANGUAGE GeneralizedNewtypeDeriving #-} -- needed for 'deriving' in newtype

-- The point of HandleIO is to create a 'safe' IO monad
-- where only certain actions are permitted

module HandleIO
(
  HandleIO
, Handle
, IOMode(..)
, runHandleIO
, openFile
, hClose
, hPutStrLn
) where

import System.IO (Handle, IOMode(..))
import qualified System.IO
import Control.Monad.Trans (MonadIO(..))
import System.Directory (removeFile)

{-
class Monad m => MonadIO m where
  liftIO :: IO a -> m a
-}

newtype HandleIO a = HandleIO { runHandleIO :: IO a }
  deriving Monad

openFile :: FilePath -> IOMode -> HandleIO Handle
openFile path mode = HandleIO(System.IO.openFile path mode)

hClose :: Handle -> HandleIO ()
hClose = HandleIO . System.IO.hClose

hPutStrLn :: Handle -> String -> HandleIO ()
hPutStrLn h s = HandleIO(System.IO.hPutStrLn h s)


safeHello :: FilePath -> HandleIO ()
safeHello path = do
  h <- openFile path WriteMode
  hPutStrLn h "Hello World"
  hClose h

instance MonadIO HandleIO where
  liftIO = HandleIO

tidyHello :: FilePath -> HandleIO ()
tidyHello path = do
  safeHello path
  liftIO (removeFile path) -- now we can do unexpected IO with our safe monad
















