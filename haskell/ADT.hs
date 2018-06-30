{-
newtype Counter = Counter { unCounter :: Int }

new :: Counter
new = Counter 0

get :: Counter -> Int
get = unCounter 

inc :: Counter -> Counter
inc (Counter n) = Counter (n + 1)


ex = get (inc new)
-}

{-
class Counter a where
    new :: a
    get :: a -> Int
    inc :: a -> a 

newtype Count = Count { unCount :: Int }

instance Counter Count where
    new = Count 0
    get = unCount
    inc (Count n) = Count (n + 1)

-}

data Counter a = Counter
    {   new :: a
    ,   get :: a -> Int
    ,   inc :: a -> a
    }  
    

newtype Count = Count { unCount :: Int }

count :: Counter Count
count = Counter 
    { new = Count 0
    , get = unCount
    , inc = \(Count n) -> Count (n + 1)
    }


ex = (get count) ((inc count) (new count))
    
