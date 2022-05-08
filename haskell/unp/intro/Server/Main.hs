module Main 
  ( main
  ) where

import Control.Exception
import Control.Monad

import Network.Socket

main :: IO ()
main = do
  let fam :: Family
      fam = AF_INET
 
  let typ :: SocketType
      typ = Stream

  let num :: ProtocolNumber
      num = 0

  sock <- socket fam typ num

  let info :: AddrInfo
      info = defaultHints
        { addrFlags = [AI_PASSIVE]
        , addrFamily = AF_INET
        , addrProtocol = 13
        }

  info' <- head <$> (getAddrInfo (Just info) Nothing (Just "13")) :: IO AddrInfo

  let sockAddr :: SockAddr
      sockAddr = addrAddress info'

  bind sock sockAddr

  listen sock 10

  forever $ do
    
    (conn, peer) <- accept sock

    putStrLn $ "Connection from " ++ show peer

