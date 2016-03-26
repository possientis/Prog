import System.IO
import Data.Char(toUpper)


main::IO()
main = do
  inh     <- openFile "input.txt" ReadMode
  outh    <- openFile "output.txt" WriteMode  
  inpStr  <- hGetContents inh -- lazy string, does not matter how big file is
  let result = processData inpStr
  hPutStr outh result -- transferring string to output file
  hClose inh
  hClose outh


processData :: String -> String
processData = map toUpper


