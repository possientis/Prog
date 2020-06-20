module  Heap
    (   Heap 
    ,   newHeap
    ,   findVal
    ,   heapAlloc
    ,   heapWrite
    )   where

import Data.Map as M

import Addr
import Value

data Heap = Heap
    { next :: Addr
    , memory :: Map Addr Value
    }

findVal :: Addr -> Heap -> Value
findVal addr heap
    | addr >= next heap  = error "unallocated memory access"
    | otherwise = case M.lookup addr (memory heap) of
        Nothing -> error "memory corruption error"
        Just v  -> v 

heapAlloc :: Heap -> (Heap, Addr)
heapAlloc heap = (heap', addr) where
    addr  = next heap
    heap' = Heap 
        { next = inc addr 
        , memory = insert addr mkNil (memory heap)
        }

newHeap :: Heap
newHeap = Heap
    { next = start
    , memory = M.empty
    }

heapWrite :: Heap -> Addr -> Value -> Heap
heapWrite heap addr v = if addr >= next heap
    then error "heapWrite: illegal memory access"
    else heap { memory = M.insert addr v (memory heap) } 


