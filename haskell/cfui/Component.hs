module  Component
    (   Component
    ,   explore
    )   where

import Data.IORef
import Control.Monad
import Control.Comonad

import UI
import Pairing
import Console

type Component base w m a = w (UI base m a)

explore :: (Comonad w, Pairing m w) => Component IO w m Console -> IO ()
explore component = do
    ref <- newIORef component
    forever $ do
        space <- readIORef ref
        let send baction = do
            action <- baction
            writeIORef ref (move space action)
        let Console text action = extract space send

        putStrLn text
        input <- getLine
        action input


