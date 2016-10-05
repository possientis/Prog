{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Concurrent.STM
import Control.Monad

data Item = Scroll
          | Wand
          | Banjo
            deriving (Eq, Ord, Show)

newtype Gold = Gold Int
  deriving (Eq, Ord, Show, Num)

newtype HitPoint = HitPoint Int
  deriving (Eq, Ord, Show, Num)

type Inventory = TVar [Item]
type Health = TVar HitPoint
type Balance = TVar Gold

data Player = Player {
      balance :: Balance,
      health :: Health,
      inventory :: Inventory
}

basicTransfer :: Num a => a -> TVar a -> TVar a -> STM ()
basicTransfer qty fromBal toBal = do
  fromQty <- readTVar fromBal
  toQty   <- readTVar toBal
  writeTVar fromBal (fromQty - qty)
  writeTVar toBal   (toQty + qty)

transferTest :: STM (Gold, Gold)
transferTest = do
  alice <- newTVar (12 :: Gold)
  bob   <- newTVar 4
  basicTransfer 3 alice bob
  liftM2 (,) (readTVar alice) (readTVar bob)

-- atomically :: STM a -> IO a
test1 = do
  atomically transferTest -- (Gold 9, Gold 7)

-- takeWhile :: (a -> Bool) -> [a] -> [a]
-- does the job but most likely inefficient
removeInv :: Eq a => a -> [a] -> Maybe [a]
removeInv x xs =
  let ys = takeWhile (/= x) xs
  in if length ys == length xs 
        then Nothing
        else Just $ ys ++ drop (length ys + 1) xs
     

test2 = [0,4,1,5,2,4,7,8,2,0]
test3 = takeWhile (/= 2) test2 -- [0,4,1,5] 
test4 = removeInv 2 test2

maybeGiveItem item fromInv toInv = do
  fromList <- readTVar fromInv
  case removeInv item fromList of
    Nothing -> return False
    Just newList -> do
      writeTVar fromInv newList
      destItems <- readTVar toInv
      writeTVar toInv (item : destItems)
      return True





