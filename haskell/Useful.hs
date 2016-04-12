import System.FilePath (replaceExtension)
import System.Directory (doesFileExist, renameDirectory, renameFile)
import Glob (namesMatching) -- need to solev failure

renameWith :: (FilePath -> FilePath) -> FilePath -> IO FilePath
renameWith f path = do
  let path' = f path
  rename path path'
  return path'

rename :: FilePath -> FilePath -> IO ()
rename old new = do
  isFile <- doesFileExist old
  let f = if isFile then renameFile else renameDirectory
  f old new
