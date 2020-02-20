module Conditional
    (   conditional
    )   where

import Control.Lens


conditional :: Lens' (Bool,a,a) a
conditional = lens 
    (\s -> if view _1 s then view _2 s else view _3 s) 
    (\s a -> if view _1 s then set _2 a s else set _3 a s)
