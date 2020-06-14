module  State
    (   State
    ,   initState
    ,   getEnv
    ,   getHeap
    ,   setHeap
    ,   setEnv
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

setEnv :: Env -> State -> State
setEnv e s = s { env = e }

initState :: State
initState = State
    { heap = newHeap
    , env  = newEnv
    }
