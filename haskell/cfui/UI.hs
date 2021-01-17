module  UI
    (   UI
    )   where

type UI base action a = (base (action ()) -> base ()) -> a
