module NiceFork
(
ThreadManager
, newManager
, forkManaged
, getStatus
, waitFor
, waitAll
) where

import Control.Concurrent
import Control.Exception (SomeException(..), try)
import qualified Data.Map as M

data ThreadStatus = Running
                  | Finished            -- terminated normally
                  | Threw SomeException -- killed by uncaught exception
                    deriving (Eq, Show)

instance Eq SomeException where

-- | Create a new thread manager.
newManager :: IO ThreadManager
newManager = fmap Mgr (newMVar M.empty)   -- newMVar :: a -> IO (MVar a)

-- | Create a new managed thread.
forkManaged :: ThreadManager -> IO () -> IO ThreadId
forkManaged = undefined

-- | Immediately return the status of a managed thread.
getStatus :: ThreadManager -> ThreadId -> IO (Maybe ThreadStatus)
getStatus = undefined

-- | Block until a specific managed thread terminates.
waitFor :: ThreadManager -> ThreadId -> IO (Maybe ThreadStatus)
waitFor =  undefined

-- | Block until all managed threads terminate.
waitAll :: ThreadManager -> IO ()
waitAll = undefined

newtype ThreadManager =
  Mgr (MVar (M.Map ThreadId (MVar ThreadStatus)))
  
