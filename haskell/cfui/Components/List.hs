module  Components.List
    (   main
    )   where

import Control.Monad.State.Class

import UI
import Store
import State
import Console
import Component

-- type Component base w m a = w (UI base m a)
-- base = IO            : base monad
-- w = Store [String]   : space comonad
-- m = State [String]   : action monad
-- a = Console
listComponent :: Component IO (Store [String]) (State [String]) Console
listComponent = Store render initStore where
    initStore :: [String]
    initStore = []

    -- type UI base action a = (action () -> base ()) -> a
    -- base = IO
    -- action = State [String]
    -- a = Console
    -- send :: State [String] () -> IO ()
    render :: [String] -> UI IO (State [String]) Console
    render xs send = Console
        { text   = "I have received:\n" ++ show xs
        , action = \input -> send $
            if input == "" 
                then return $ put [] 
                else return $ modify (++[input])
        }

main :: IO ()
main = explore listComponent
