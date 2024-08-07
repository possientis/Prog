import System.IO
import Control.Monad

dumpFile 
    :: Handle 
    -> FilePath 
    -> Integer 
    -> IO ()
dumpFile handle filename lineNumber = do
    end <- hIsEOF handle
    when (not end) $ do
        line <- hGetLine handle
        putStrLn $ filename ++ ":" ++ show lineNumber ++ ": " ++ line
        dumpFile handle filename $ lineNumber + 1


main :: IO ()
main = do
    hPutStr stderr "Type a filename: "
    filename <- getLine
    handle   <- openFile filename ReadMode
    dumpFile handle filename 1
    hClose handle
