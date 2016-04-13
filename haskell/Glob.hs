module Glob (namesMatching) where

import System.Directory (
  doesDirectoryExist, 
  doesFileExist,
  getCurrentDirectory, 
  getDirectoryContents)

import System.FilePath (dropTrailingPathSeparator, splitFileName, (</>))
import Control.Exception
import Control.Monad (forM)
import GlobRegex (matchesGlob)


str1 = "foo" </> "bar"  -- foo/bar
str2 = "foo/" </> "bar" -- foo/bar
str3 = dropTrailingPathSeparator "foo/" -- foo
str4 = dropTrailingPathSeparator "foo" -- foo
list1 = splitFileName "foo/bar/Quux.hs" -- ("foo/bar/","Quux.hs")


isPattern :: String -> Bool
isPattern = any (`elem` "[*?")  -- whether string contains chars '[', '*' or '?'

namesMatching :: String -> IO [String]
namesMatching pat
  | not (isPattern pat) = do
    exists <- doesNameExist pat
    return (if exists then [pat] else [])
  | otherwise = do
    case splitFileName pat of
      ("", baseName) -> do
        curDir <- getCurrentDirectory
        listMatches curDir baseName
      (dirName, baseName) -> do
        dirs <- if isPattern dirName
                then namesMatching (dropTrailingPathSeparator dirName)
                else return [dirName]
        let listDir = if isPattern baseName
                      then listMatches
                      else listPlain
        pathNames <- forM dirs $ \dir -> do
                        baseNames <- listDir dir baseName
                        return (map (dir </>) baseNames)
        return (concat pathNames) 



doesNameExist :: FilePath -> IO Bool
doesNameExist name = do
  fileExists <- doesFileExist name
  if fileExists
    then return True
    else doesDirectoryExist name


ignore :: SomeException -> IO [String]
ignore = const (return [])


listMatches :: FilePath -> String -> IO [String]
listMatches dirName pat = do
  dirName' <- if null dirName
              then getCurrentDirectory
              else return dirName
  handle ignore $ do -- had to define 'ignore' in order to spell out Exception type
    names <- getDirectoryContents dirName'
    let names' =  if isHidden pat
                  then filter isHidden names
                  else filter (not . isHidden) names
    return (filter (`matchesGlob` pat) names') 

isHidden ('.':_)  = True
isHidden _        = False


listPlain :: FilePath -> String -> IO [String]
listPlain dirName baseName = do
  exists <- if null baseName
            then doesDirectoryExist dirName
            else doesNameExist (dirName </> baseName)
  return (if exists then [baseName] else [])





