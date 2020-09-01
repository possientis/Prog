{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ConstraintKinds        #-}

module  Prim
    (   askEnv
    ,   find
    ,   alloc
    ,   write
    ,   localEnv
    )   where

import Env
import Log
import Addr
import Heap
import Value
import Error

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except

-- Returns current environment
askEnv :: (MonadReader Env m) => m Env
askEnv  = ask

-- Retrieves value stored in the Heap at given memory address
find :: (MonadState Heap m, MonadError Error m) => Addr -> m Value
find addr = do
    heap <- get
    case findVal addr heap of
        Left e  -> throwError $ errorFind addr e
        Right v -> return v

-- Allocates new memory address
alloc :: (MonadState Heap m) => m Addr
alloc = do
    (heap,addr) <- heapAlloc <$> get
    put heap
    return addr

-- Write a value at a given memory address
write 
    :: (MonadState Heap m, MonadWriter Log m, MonadError Error m) 
    => Addr 
    -> Value 
    -> m ()
write addr v = do
    heap <- get
    case heapWrite addr v heap of
        Left e -> throwError $ errorWrite addr e
        Right heap' -> do
            put heap'
            tell ["write at address " ++ show addr ++ ": " ++ show v]

-- Run computation in a local environment
localEnv 
    :: (MonadReader Env m) 
    => Env 
    -> m Value 
    -> m Value
localEnv env ev = local (const env) ev

errorFind :: Addr -> Error -> Error
errorFind addr e 
    = mkError ("find: failed to read memory at address " ++ show addr) <> e

errorWrite :: Addr -> Error -> Error
errorWrite addr e 
    = mkError ("write: failed to write memory at address " ++ show addr) <> e

