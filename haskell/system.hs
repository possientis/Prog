import System.Cmd
import System.Directory(
  setCurrentDirectory, 
  getCurrentDirectory,
  getDirectoryContents,
  getHomeDirectory)
import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))


main = do
  putStrLn "ls -l /usr ..."
  rawSystem "ls" ["-l", "/usr"]
  putStrLn "ls ..."
  rawSystem "ls" []
  putStrLn "running 'getCurrentDirectory ...'"
  res <- getCurrentDirectory; print res
  putStrLn "run 'setCurrentDirectory ..'"
  setCurrentDirectory ".."
  putStrLn "running 'getCurrentDirectory ...'"
  res <- getCurrentDirectory; print res
  putStrLn "running 'getDirectoryContents ...'"
  list <- getDirectoryContents "."; print $ filter (`notElem` [".",".."]) list
  putStrLn "running 'getHomeDirectory ...'"
  res <- getHomeDirectory; print res
  exitWith (ExitFailure 5)
  
