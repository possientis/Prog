{-
 - $ ghc -c NumCapabilities.hs
 - $ ghc -threaded -o NumCapabilities NumCapabilities.o
 - $ ./NumCapabilities +RTS -N4 -RTS foo
 -}

import GHC.Conc (numCapabilities)
import System.Environment (getArgs)

main = do
  args <- getArgs
  putStrLn $ "command line arguments: " ++ show args
  putStrLn $ "number of cores: " ++ show numCapabilities
