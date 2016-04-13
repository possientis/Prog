module RecursiveContents (getRecursiveContents) where

import Control.Monad (forM)
import System.Directory (doesDirectoryExist, getDirectoryContents)
import System.FilePath ((</>))

getRecursiveContents :: FilePath -> IO [FilePath]
getRecursiveContents topdir = do
  names <- getDirectoryContents topdir                    -- getDirectoryContents :: FilePath -> IO [FilePath]
  let properNames = filter (`notElem` [".", ".."]) names  -- removing "." and ".." from names (otherwise recursion will be infinite)
  paths <- forM properNames $ \name -> do                 -- forM :: Monad m => [a] -> (a -> m b) -> m [b] , 'flip' of mapM :: Monad m => (a -> m b) -> [a] -> m [b]
    let path = topdir </> name                            -- (</>) :: FilePath -> FilePath -> FilePath
    isDirectory <- doesDirectoryExist path                -- doesDirectoryExist :: FilePath -> IO Bool
    if isDirectory
      then getRecursiveContents path
      else return [path]
  return (concat paths)                                   -- concat :: [[a]] -> [a]



