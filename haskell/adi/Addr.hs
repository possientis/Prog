module  Addr
    (   Addr 
    ,   inc 
    ,   dec
    ,   start
    )   where

newtype Addr = Addr { unAddr :: Integer }
    deriving (Eq, Ord)

instance Show Addr where
    show = show . unAddr

inc :: Addr -> Addr
inc addr = Addr (unAddr addr + 1)

dec :: Addr -> Addr
dec addr = Addr (unAddr addr - 1)

start :: Addr
start = Addr 0


