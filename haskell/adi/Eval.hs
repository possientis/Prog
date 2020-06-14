{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval
    (   Eval    (..)    -- TODO: hide 
    ,   alloc
    ,   askEnv
    ,   find
    ,   write
    ,   localEnv
    )   where

import Env
import Addr
import Heap
import State
import Value

import Data.Functor.Identity
import Control.Monad.Trans.State hiding (State)

newtype Eval a = Eval { unEval :: StateT State Identity a } 
    deriving (Functor, Applicative, Monad)

askEnv :: Eval Env
askEnv  = Eval $ gets getEnv 

find :: Addr -> Eval Value
find addr = Eval $ do
    heap <- gets getHeap
    return $ findVal heap addr 

alloc :: Eval Addr
alloc = Eval $ do
    s <- get
    let heap = getHeap s
    let (heap',addr) = heapAlloc heap
    let s' = setHeap heap' s
    put s'
    return addr

write :: Addr -> Value -> Eval ()
write addr v = Eval $ do
    s <- get
    let heap = getHeap s
    let heap' = heapWrite heap addr v
    let s' = setHeap heap' s
    put s'
    return () 

-- run computation in a local environment
localEnv :: Env -> Eval Value -> Eval Value
localEnv env ev = Eval $ do
    s0 <- get
    let env0 = getEnv s0
    let s1 = setEnv env s0
    put s1
    v <- unEval ev
    s2 <- get
    let s3 = setEnv env0 s2
    put s3
    return v
