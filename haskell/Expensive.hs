import Control.Concurrent

notQuiteRight = do
  mv <- newEmptyMVar
  forkIO $ expensiveComputation mv
  someOtherActivity
  result <- takeMVar mv
  print result

-- lazy so actual computation will occur in main thread
-- defeating the purpose of forking
expensiveComputation mv = do
  let a = "this is "
      b = "not really "
      c = "all that expensive"
  putMVar mv (a ++ b ++ c)


someOtherActivity = undefined
