import Control.Concurrent.STM
import Control.Monad
import GHC.Conc (unsafeIOToSTM)

someAction ::IO a
someAction = undefined

stmTransaction :: STM (IO a)
stmTransaction  = return someAction

-- atomically :: STM a -> IO a
-- join :: Monad m => m (m a) -> m a
doSomething :: IO a
doSomething = join (atomically stmTransaction)


launchTorpedos :: IO ()
launchTorpedos = undefined

doStuff = undefined
mightRetry = undefined

notActuallyAtomic = do
  doStuff
  unsafeIOToSTM launchTorpedos
  mightRetry  -- if this cause ou transaction to restart,
              -- will launchTorpedos mpre than once
