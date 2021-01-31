module  Components.Files
    (
    )   where

import UI
import Store
import State
import Console
import Component

_filesComponent :: Component IO (Store [String]) (State [String]) Console
_filesComponent = Store render initStore where
    initStore :: [String]
    initStore = []

    render :: [String] -> UI IO (State [String]) Console
    render = undefined
