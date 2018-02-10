
-- use -Wno-deprecations option
import Control.Monad
import Data.Attoparsec -- deprecated
import qualified Data.Attoparsec.Char8 as A -- deprecated

import Data.ByteString.Char8

data Action 
    = Success
    | KeepAlive
    | NoResource
    | Hangup
    | NewLeader
    | Election
    deriving Show

type Sender = ByteString
type Payload = ByteString

data Message = Message
    { action  :: Action
    , sender  :: Sender
    , payload :: Payload
    } deriving Show

proto :: Parser Message
proto = do
    act <- paction
    send <- A.takeTill (== '.')
    body <- A.takeTill (A.isSpace)
    A.endOfLine
    return $ Message act send body


paction :: Parser Action
paction = do
    c <- anyWord8
    case c of
        1 -> return Success
        2 -> return KeepAlive
        3 -> return NoResource
        4 -> return Hangup
        5 -> return NewLeader
        6 -> return Election
        _ -> mzero

-- don't have full message
main :: IO ()
main = do
    let msgText = pack  $  "\x01\x6c\x61\x70\x74\x6f\x70\x2e\x33\x2e"
                        ++ "\x31\x34\x31\x35\x39\x32\x36\x35\x32"
    let msg = parseOnly proto msgText
    print msg



