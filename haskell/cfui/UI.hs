module  UI
    (   UI
    )   where

type UI base action a = (action () -> base ()) -> a
