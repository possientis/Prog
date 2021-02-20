module  UI
    (   UI
    )   where

type UI base m a = (base (m ()) -> base ()) -> a
