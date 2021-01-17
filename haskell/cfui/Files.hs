module  Files
    (
    )   where

import Component

filesComponent :: Component IO (Store [String]) (State [String]) Console
filesComponent = Store render initStore where
    initStore :: [String]
    initStore = []

    render :: [String] -> UI IO (State [String]) Console
    render = undefined
