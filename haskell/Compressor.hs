import Control.Concurrent (forkIO)
import Control.Exception (handle)
import Control.Monad (forever)
import qualified Data.ByteString.Lazy as L
import System.Console.Readline (readline)
import Codec.Compression.GZip (compress)

main = do
  maybeLine <- readline "Enter a file to compress> "
  case maybeLine of
    Nothing -> return () -- user entered EOF
    Just "" -> return () -- treat no name as "want to quit"
    Just name -> do
        content <- L.readFile name
        -- we are using lazy byte strings. Hence the main thread
        -- is simply opening the file. The actual reading is done
        -- (on demand) by the new thread.
        forkIO (compressFile name content)
        main
  where compressFile path = L.writeFile (path ++ ".gz") . compress
