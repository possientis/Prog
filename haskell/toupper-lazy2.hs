import System.IO
import Data.Char(toUpper)

main = do
  inh <- openFile "input.txt" ReadMode
  outh <- openFile "output.txt" WriteMode
  inpStr <- hGetContents inh
  hPutStr outh (map toUpper inpStr)
  hClose inh  -- make sure you no longer need handle before closing.
              -- lazy evaluation can trick you there
  hClose outh
