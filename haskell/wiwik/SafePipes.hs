import Pipes
import Pipes.Safe                   -- libghc-pipes-safe-dev

import Data.ByteString.Char8
import System.Timeout (timeout)
import qualified System.ZMQ4 as ZMQ -- libghc-zeromq4-haskell-dev 


data Opts = Opts 
    { _addr     :: String   -- ^ ZMQ socket address
    , _timeout  :: Int      -- ^ Time in milliseconds for socket timeout
    }

recvTimeout :: Opts -> ZMQ.Socket a -> Producer ByteString (SafeT IO) ()
recvTimeout opts sock = do
    body <- liftIO $ timeout (_timeout opts) (ZMQ.receive sock)
    case body of
        Just msg -> do
            liftIO $ ZMQ.send sock msg []
            yield msg
            recvTimeout opts sock   
        Nothing -> liftIO $ print "socket timed out"

-- FAILURE
