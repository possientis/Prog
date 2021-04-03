module  Lab
    (   main
    )   where

import Free
import Teletype

echo :: Free Teletype ()
echo = do
    msg <- readLine 
    writeLine msg

main :: IO ()
main = runTeletype echo
