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
import Error

data Heap = Heap
    { next :: Addr
    , memory :: Map Addr Value
    }

maxAddr :: Heap -> Maybe Addr
maxAddr heap
    | next heap == start = Nothing
    | otherwise          = Just . dec . next $ heap

instance Show Heap where
    show = show . M.toList . memory

findVal :: Addr -> Heap -> Either Error Value
findVal addr heap
    | addr >= next heap  = Left $ errorFindVal1 addr heap
    | otherwise = case M.lookup addr (memory heap) of
        Nothing -> Left $ errorFindVal2 addr heap
        Just v  -> Right v 

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

heapWrite :: Addr -> Value -> Heap -> Either Error Heap
heapWrite addr v heap = if addr >= next heap
    then Left $ errorHeapWrite addr v heap
    else Right heap { memory = M.insert addr v (memory heap) } 

errorFindVal1 :: Addr -> Heap -> Error
errorFindVal1 addr heap = mkError $ unlines 
    [ "findVal: illegal memory access. Attempting to read memory at address "
    ++ show addr 
    ++ " while " 
    ++ maybe "the heap is empty." 
        (\m -> "the maximum allowable address is " ++ show m ++ ".")
        (maxAddr heap)
    , "The current heap state is as follows:"
    , show heap
    ]

errorFindVal2 :: Addr -> Heap -> Error
errorFindVal2 addr heap = mkError $ unlines 
    [ "findVal: memory corruption error. Attempting to read memory at address "
    ++ show addr 
    ++ " but failed to retrieve data." 
    , "The current heap state is as follows:"
    , show heap
    ]

errorHeapWrite :: Addr -> Value -> Heap -> Error
errorHeapWrite addr v heap = mkError $ unlines 
    [ "heapWrite: illegal memory access. Attempting to write memory at address "
    ++ show addr 
    ++ " the value "
    ++ show v
    ++ " while " 
    ++ maybe "the heap is empty." 
        (\m -> "the maximum allowable address is " ++ show m ++ ".")
        (maxAddr heap)
    , "The current heap state is as follows:"
    , show heap
    ]
