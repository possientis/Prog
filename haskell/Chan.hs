-- IPC using channels
import Control.Concurrent
import Control.Concurrent.Chan

chanExample = do
  ch <- newChan
  forkIO $ do
    writeChan ch "hello world"
    writeChan ch "now i quit"
  -- main thread
  readChan ch >>= print
  readChan ch >>= print

main = chanExample
