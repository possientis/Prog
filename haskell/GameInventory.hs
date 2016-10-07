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

-- newTVar :: a -> STM (TVar a)
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

-- readTVar :: TVar a -> STM a
-- writeTVar :: TVar a -> a -> STM ()

maybeGiveItem :: Eq a => a -> TVar [a] -> TVar [a] -> STM Bool
maybeGiveItem item fromInv toInv = do
  fromList <- readTVar fromInv
  case removeInv item fromList of
    Nothing -> return False
    Just newList -> do
      writeTVar fromInv newList
      destItems <- readTVar toInv
      writeTVar toInv (item : destItems)
      return True

maybeSellItem :: Item -> Gold -> Player -> Player -> STM Bool
maybeSellItem item price buyer seller = do
  given <- maybeGiveItem item (inventory seller) (inventory buyer)
  if given
    then do
      basicTransfer price (balance buyer) (balance seller)
      return True
    else return False


giveItem :: Item -> Inventory -> Inventory -> STM ()
giveItem item fromInv toInv = do
  fromList <- readTVar fromInv
  case removeInv item fromList of
    Nothing -> retry  -- will block (until something changes)
    Just newList -> do
      writeTVar fromInv newList
      readTVar toInv >>= writeTVar toInv . (item :)

transfer :: Gold -> Balance -> Balance -> STM ()
transfer qty fromBal toBal = do
  fromQty <- readTVar fromBal
  when (qty > fromQty) $
    retry               -- will block (until something changes)
  writeTVar fromBal (fromQty - qty)
  readTVar toBal >>= writeTVar toBal . (qty +)

-- will blocl until both the seller has item and buyer has money
sellItem :: Item -> Gold -> Player -> Player -> STM ()
sellItem item price buyer seller = do
  giveItem item (inventory seller) (inventory buyer)
  transfer price (balance buyer) (balance seller)

crummyList :: [(Item, Gold)] -> Player -> Player
           -> STM (Maybe (Item, Gold))
crummyList list buyer seller = go list
  where go []                 = return Nothing
        go (this@(item,price) : rest) = do
          sellItem item price buyer seller
          return (Just this)
          `orElse`  -- orElse :: STM a -> STM a -> STM a
            go rest

maybeSTM :: STM a -> STM (Maybe a)
maybeSTM m = (Just `liftM` m) `orElse` return Nothing

shoppingList :: [(Item, Gold)] -> Player -> Player
             -> STM (Maybe (Item, Gold))
shoppingList list buyer seller = maybeSTM . msum $ map sellOne list
  where sellOne this@(item,price) = do
          sellItem item price buyer seller
          return this

maybeM :: MonadPlus m => m a -> m (Maybe a)
maybeM m = (Just `liftM` m) `mplus` return Nothing


