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

explore 
    :: (Comonad w, Pairing m w) 
    => Component IO w m Console 
    -> IO ()
explore component = do
    ref <- newIORef component
    forever $ do
        space <- readIORef ref
        runConsole $ extract space $ \k -> do
            act <- k
            writeIORef ref (move space act)
