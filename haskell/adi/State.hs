module  State
    (   State   (..)    -- TODO : hide
    )   where

import Env
import Heap

data State = State
    {   heap :: Heap
    ,   env  :: Env
    }


