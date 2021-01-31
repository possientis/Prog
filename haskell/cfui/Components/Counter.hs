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

main :: IO ()
main = explore counterComponent

_main :: IO ()
_main = do
    ref <- newIORef 0
    forever (ui ref)

ui :: IORef Int -> IO ()
ui ref = do
    counter <- readIORef ref 
    putStrLn (show counter)
    _ <- getLine
    writeIORef ref (counter + 1)

counterComponent :: Component IO Stream Sequence Console
counterComponent = unfoldStream 0 (\state -> (render state, state + 1))
    where
        render :: Int -> UI IO Sequence Console
        render state = \send -> 
            Console
                (show state)                                 
                (\_input -> send $ return $ (Next (End ()))) 
