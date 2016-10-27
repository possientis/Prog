import System.Environment (getArgs)     -- getArgs :: IO [String]
import System.IO (readFile)             -- readFile :: FilePath -> IO String
import System.Directory (doesFileExist) -- doesFileExist :: FilePath -> IO Bool
import Control.Exception (IOException, catch) 


main :: IO ()
main = main2





main1 :: IO ()
main1 = do
  (filename:_) <- getArgs         
  fileExists <- doesFileExist filename
  if fileExists
    then do
      contents <- readFile filename -- this is why we need 'do'  
      putStrLn $ "The file has " ++ show (length (lines contents)) ++ " lines!"
    else
       putStrLn $ "The file does not exist!"

main2 :: IO ()
main2 = toTry `catch` handler -- Exception e => IO a -> (e -> IO a) -> IO a

toTry :: IO()
toTry = do
  (filename:_) <- getArgs         
  contents <- readFile filename
  putStrLn $ "The file has " ++ show (length (lines contents)) ++ " lines!"

handler :: IOException -> IO ()
handler e = putStrLn "Whoops, had some trouble !"

