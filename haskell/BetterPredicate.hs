import Control.Monad (filterM)
import System.Directory (Permissions(..), getModificationTime, getPermissions)
import Data.Time.Clock
import System.FilePath (takeExtension)
import Control.Exception (bracket, handle, SomeException)
import System.IO (IOMode(..), hClose, hFileSize, openFile)

-- the function we wrote earlier
import RecursiveContents (getRecursiveContents)

type Predicate  =   FilePath      -- path to directory entry
                ->  Permissions   -- permissions
                ->  Maybe Integer -- file size (nothing if not file)
                ->  UTCTime 
                ->  Bool   


betterFind :: Predicate -> FilePath -> IO [FilePath]
betterFind p path = getRecursiveContents path >>= filterM check
  where check name = do
          perms     <- getPermissions name
          size      <- getFileSize name
          modified  <- getModificationTime name
          return (p name perms size modified)
               
-- basic, but will throw exception on non-existent file, or pipes etc
simpleFileSize :: FilePath -> IO Integer
simpleFileSize path = do
  h <- openFile path ReadMode
  size <- hFileSize h
  hClose h
  return size


ignore :: SomeException -> IO (Maybe Integer)
ignore = const(return Nothing)

-- better as it throws no exception. However, still unsatisfactory
-- as hFileSize will throw on a pipe (say) and exception handler
-- will be called without any 'finally' clause releasing the ressource.
-- Hence on a big search involving many 'files' for which hFileSize 
-- will fail, we could quickly exhaust linux limit on the number
-- of open file descriptors,
saferFileSize :: FilePath -> IO (Maybe Integer)
saferFileSize path = handle ignore $ do
  h <- openFile path ReadMode
  size <- hFileSize h
  hClose h
  return (Just size)

-- Exception handling with a 'finally' clause to make sure
-- resource gets released. Using the 'bracket' function
-- bracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
-- first argument: the 'acquire' action
-- second argument: the 'release' action
-- third argument: the 'use' action
-- bracket ensure that release is called, whether or not 'use' throws

getFileSize :: FilePath -> IO (Maybe Integer)
getFileSize path = handle ignore $
  bracket (openFile path ReadMode) hClose $ \h -> do
    size <- hFileSize h
    return (Just size)

myTest path _ (Just size) _ =
  takeExtension path == ".cpp" && size < 512
myTest path _ _ _ = False

type InfoP a  = FilePath
              -> Permissions
              -> Maybe Integer
              -> UTCTime
              -> a

pathP :: InfoP FilePath -- otherwise compiler would infer very general type
pathP path _ _ _ = path

sizeP :: InfoP Integer
sizeP _ _ (Just size) _ = size
sizeP _ _ Nothing     _ = -1


equalP :: (Eq a) => InfoP a -> a -> InfoP Bool
equalP f k = \w x y z -> f w x y z == k 

equalP' :: (Eq a) => InfoP a -> a -> InfoP Bool
equalP' f k w x y z = f w x y z == k 











