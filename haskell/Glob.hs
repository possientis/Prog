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
    return [] -- to be completed



doesNameExist :: FilePath -> IO Bool
doesNameExist name = do
  fileExists <- doesFileExist name
  if fileExists
    then return True
    else doesDirectoryExist name


