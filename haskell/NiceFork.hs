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
forkManaged (Mgr mgr) body =
  modifyMVar mgr $ \m -> do -- modifyMVar :: MVar a -> (a -> IO (a, b)) -> IO b
    state <- newEmptyMVar   -- newEmptyMVar :: IO (MVar a)
    tid <- forkIO $ do      -- forkIO :: IO () -> IO ThreadId
      result <- try body    -- try :: GHC.Exception.Exception e => IO a -> IO (Either e a)
      putMVar state (either Threw (const Finished) result)  -- const :: a -> b -> a
    return (M.insert tid state m, tid)  -- either :: (a -> c) -> (b -> c) -> Either a b -> c

-- | Immediately return the status of a managed thread.
getStatus :: ThreadManager -> ThreadId -> IO (Maybe ThreadStatus)
getStatus (Mgr mgr) tid =
  modifyMVar mgr $ \m ->
    case M.lookup tid m of
      Nothing -> return (m, Nothing)
      Just st -> tryTakeMVar st >>= \mst -> case mst of
                  Nothing -> return (m, Just Running)
                  Just sth -> return (M.delete tid m, Just sth)

-- | Block until a specific managed thread terminates.
waitFor :: ThreadManager -> ThreadId -> IO (Maybe ThreadStatus)
waitFor (Mgr mgr) tid = do
  maybeDone <- modifyMVar mgr $ \m ->
    return $ case M.updateLookupWithKey (\_ _ -> Nothing) tid m of
      (Nothing, _) -> (m, Nothing)
      (done, m') -> (m', done)
  case maybeDone of
    Nothing -> return Nothing
    Just st -> Just `fmap` takeMVar st

-- | Block until all managed threads terminate.
waitAll :: ThreadManager -> IO ()
waitAll (Mgr mgr) = modifyMVar mgr elems >>= mapM_ takeMVar
  where elems m = return (M.empty, M.elems m)

newtype ThreadManager =
  Mgr (MVar (M.Map ThreadId (MVar ThreadStatus)))
  
