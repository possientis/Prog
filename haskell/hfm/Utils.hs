module Utils
  ( logMessage
  ) where

import Lang.App
import Lang.Logger hiding (logMessage)
import qualified Lang.Logger as L (logMessage)

logMessage :: LogLevel -> Message -> App ()
logMessage  lvl msg = evalLogger (L.logMessage lvl msg)

