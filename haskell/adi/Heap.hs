module  Heap
    (   Heap 
    ,   newHeap
    ,   find
    ,   alloc
    )   where

import Data.Map as M

import Addr
import Value

data Heap = Heap
    { next :: Addr
    , memory :: Map Addr Value
    }

find :: Heap -> Addr -> Value
find heap addr
    | addr >= next heap  = error "unallocated memory access"
    | otherwise = case M.lookup addr (memory heap) of
        Nothing -> error "memory corruption error"
        Just v  -> v 

alloc :: Heap -> (Heap, Addr)
alloc heap = (heap', addr) where
    addr  = next heap
    heap' = Heap 
        { next = inc addr 
        , memory = insert addr valEmpty (memory heap)
        }

newHeap :: Heap
newHeap = Heap
    { next = start
    , memory = M.empty
    }



