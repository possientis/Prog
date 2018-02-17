{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

import Data.Text
import qualified Data.Configurator as C

data Config = Config
    { verbose       :: Bool
    , loggingLevel  :: Int
    , logFile       :: FilePath
    , dbHost        :: Text
    , dbUser        :: Text
    , dbDatabase    :: Text
    , dbPassword    :: Maybe Text
    } deriving (Eq, Show) 


readConfig :: FilePath -> IO Config
readConfig cfgFile = do
    cfg             <- C.load [C.Required cfgFile]
    verbose         <- C.require cfg "logging.verbose"
    loggingLevel    <- C.require cfg "logging.loggingLevel" 
    logFile         <- C.require cfg "logging.logFile"
    dbHost          <- C.require cfg "database.hostname"
    dbUser          <- C.require cfg "database.username"
    dbDatabase      <- C.require cfg "database.database"
    dbPassword      <- C.lookup  cfg "database.password"
    return $ Config {..}


main :: IO ()
main = do
    cfg <- readConfig "example.config"
    print cfg
