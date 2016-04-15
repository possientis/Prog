import Control.Monad (filterM)
import System.Directory (Permissions(..), getModificationTime, getPermissions)
import System.Time (ClockTime(..))
import System.FilePath (takeExtension)
import Control.Exception (bracket, handle)
import System.IO (IOMode(..), hClose, hFileSize, openFile)

-- the function we wrote earlier
import RecursiveContents (getRecursiveContents)

type Predicate  =   FilePath      -- path to directory entry
                ->  Permissions   -- permissions
                ->  Maybe Integer -- file size (nothing if not file)
                ->  ClockTime
                ->  Bool   

getFileSize :: FilePath -> IO (Maybe Integer)
getFileSize = undefined

betterFind :: Predicate -> FilePath -> IO [FilePath]
betterFind p path = getRecursiveContents path >>= filterM check
  where check name = do
          perms     <- getPermissions name
          size      <- getFileSize name
          modified  <- getModificationTime name
          return (p name perms size modified)
               
simpleFileSize :: FilePath -> IO Integer
simpleFileSize path = do
  h <- openFile path ReadMode
  size <- hFileSize h
  hClose h
  return size


saferFileSize :: FilePath -> IO (Maybe Integer)
saferFileSize path = handle (\_ -> return Nothing) $ do
  h <- openFile path ReadMode
  size <- hFileSize h
  hClose h
  return (Just size)




