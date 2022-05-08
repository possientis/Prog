module  Main
    (   main
    )   where

import Network
import Network.BSD
import Network.Socket
import Network.Socket.ByteString
import Network.Socket.ByteString.Lazy
import Network.Socket.Internal

main :: IO ()
main = do
    putStrLn "running..."
