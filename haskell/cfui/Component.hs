module  Component
    (   Component
    )   where

import UI

type Component base w m a = w (UI base m a)
