{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import System.IO (IOMode)
import Control.Monad.Writer

data Event  = Open FilePath IOMode
            | Put String String
            | Close String
            | GetContents String
              deriving (Show)

newtype WriterIO a = W { runW :: Writer [Event] a }
  deriving (Monad, MonadWriter [Event])

runWriterIO :: WriterIO a -> (a, [Event])
runWriterIO = runWriter . runW





