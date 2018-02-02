import Control.Monad
import Control.Concurrent
import Control.Concurrent.STM

type Account = TVar Double


transfer :: Account -> Account -> Double -> STM ()
transfer from to amount = do
    available <- readTVar from
    when (amount > available) retry
    modifyTVar from (+ (-amount))
    modifyTVar to   (+   amount)


-- Threads are scheduled non-deterministically
actions :: Account -> Account -> [IO ThreadId]
actions a b = map forkIO 
    [   atomically (transfer a b 10)
    ,   atomically (transfer a b (-20))
    ,   atomically (transfer a b 50)
        -- transfer some back
    ,   atomically (transfer a b (-30))
    ,   atomically (transfer a b 20)
    ,   atomically (transfer a b (-10))
    ]
    
main :: IO ()
main = do
    accountA <- atomically $ newTVar 60
    accountB <- atomically $ newTVar 0
    sequence_ (actions accountA accountB)
    balanceA <- atomically $ readTVar accountA
    balanceB <- atomically $ readTVar accountB

    print $ balanceA
    print $ balanceB
