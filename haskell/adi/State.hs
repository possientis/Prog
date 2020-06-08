module  State
    (   State
    ,   initState
    ,   getEnv
    ,   getHeap
    )   where

import Env
import Heap

data State = State
    {   heap :: Heap
    ,   env  :: Env
    }

getEnv :: State -> Env
getEnv = env

getHeap :: State -> Heap
getHeap = heap

initState :: State
initState = State
    { heap = newHeap
    , env  = newEnv
    }
