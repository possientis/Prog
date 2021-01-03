module  Main
    (   main
    )   where

import Data.IORef
import Control.Monad
import Control.Comonad

import Stream
import Pairing

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

type UI base m a = (m () -> base ()) -> a

type Component base w m a = w (UI base m a)

explore :: (Comonad w, Pairing m w) => Component IO w m Console -> IO ()
explore component = do
    ref <- newIORef component
    forever $ do
        space <- readIORef ref
        let send action = writeIORef ref (move space action)
        let Console text action = extract space send

        putStrLn text
        input <- getLine
        action input

data Console = Console
    { _text   :: String
    , _action :: String -> IO ()
    }

counterComponent :: Component IO Stream Sequence Console
counterComponent = unfoldStream 0 (\state -> (render state, state + 1))
    where
        render :: Int -> UI IO Sequence Console
        render state = \send -> 
            Console
                (show state)                        -- display the current value 
                (\_input -> send (Next (End ())))    -- move to next state



