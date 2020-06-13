module  State
    (   State
    ,   initState
    ,   getEnv
    ,   getHeap
    ,   setHeap
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

setHeap :: Heap -> State -> State
setHeap h s = s { heap = h } 

initState :: State
initState = State
    { heap = newHeap
    , env  = newEnv
    }
