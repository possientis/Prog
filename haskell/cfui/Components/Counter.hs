module  Components.Counter
    (   main
    )   where

import Data.IORef
import Control.Monad

import UI
import Stream
import Console
import Sequence
import Component


counterComponent :: Component IO Stream Sequence Console
counterComponent = unfoldStream 0 (\state -> (render state, state + 1))
    where
        render :: Int -> UI IO Sequence Console
        render state = \send -> 
            Console
                (show state)                                 
                (\_input -> send $ return $ (Next (End ()))) 

main :: IO ()
main = explore counterComponent

_main :: IO ()
_main = do
    ref <- newIORef 0
    forever (_ui ref)

_ui :: IORef Int -> IO ()
_ui ref = do
    counter <- readIORef ref 
    putStrLn (show counter)
    _ <- getLine
    writeIORef ref (counter + 1)


