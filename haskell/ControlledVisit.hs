module ControlledVisit(getUsefulContents, Info(..), getInfo, isDirectory) where
import Control.Monad (forM, liftM)
import System.FilePath ((</>))

import System.Directory(Permissions, getDirectoryContents, getPermissions, getModificationTime, searchable)
import Data.Time.Clock(UTCTime)
import Control.Exception (handle, bracket, SomeException)
import System.IO (hClose, hFileSize, openFile, IOMode(..)) 

data Info = Info {
  infoPath    :: FilePath
, infoPerms   :: Maybe Permissions
, infoSize    :: Maybe Integer
, infoModTime :: Maybe UTCTime
} deriving (Eq, Ord, Show)


getUsefulContents :: FilePath -> IO [String]
getUsefulContents path = do
  names <- getDirectoryContents path
  return (filter (`notElem` [".",".."]) names)

isDirectory :: Info -> Bool
isDirectory = maybe False searchable . infoPerms

maybeIO :: IO a -> IO (Maybe a)
maybeIO act = handle ((\_ -> return Nothing) :: SomeException -> IO (Maybe a))
                     (liftM Just act)

getInfo :: FilePath -> IO Info
getInfo path = do
  perms <- maybeIO (getPermissions path)
  size  <- maybeIO (bracket (openFile path ReadMode) hClose hFileSize)
  modified <- maybeIO (getModificationTime path)
  return (Info path perms size modified)
 

main = do
  infos <- traverse id "/home/john/Prog/poly"
  putStrLn (show infos)

traverse :: ([Info] -> [Info]) -> FilePath -> IO [Info]
traverse order path = do
  names <- getUsefulContents path  
  contents <- mapM getInfo (path : map (path </>) names)
  liftM concat $ forM (order contents) $ \info -> do
    if isDirectory info && infoPath info /= path
      then traverse order (infoPath info)
      else return [info]

traverseVerbose :: ([Info] -> [Info]) -> FilePath -> IO [Info]
traverseVerbose order path = do
  names <- getDirectoryContents path
  let usefulNames = filter (`notElem` [".", ".."]) names
  contents <- mapM getEntryName ("" : usefulNames)
  recursiveContents <- mapM recurse (order contents)
  return (concat recursiveContents)
  where getEntryName name = getInfo (path </> name)
        isDirectory info = case infoPerms info of
          Nothing -> False
          Just perms -> searchable perms
        recurse info = do
          if isDirectory info && infoPath info /= path
          then traverseVerbose order (infoPath info)
          else return [info]







  
