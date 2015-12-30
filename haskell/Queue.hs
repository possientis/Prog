module Queue (Queue, push, peek, pop, isEmpty, empty, toList) where

newtype Queue a = MkQueue ([a],[a])


empty :: Queue a
empty = MkQueue ([],[])

push :: Queue a -> a -> Queue a
push (MkQueue (fs,bs)) x = clean (MkQueue (fs,x:bs))

peek :: Queue a -> Maybe a
peek (MkQueue ([],[]))  = Nothing
peek (MkQueue (x:fs,bs)) = Just x

isEmpty :: Queue a -> Bool
isEmpty (MkQueue ([],[])) = True
isEmpty _  = False

clean :: Queue a -> Queue a
clean (MkQueue ([],bs)) = MkQueue (reverse bs, []) 
clean q = q

pop :: Queue a -> Queue a
pop (MkQueue ([],[])) = empty
pop (MkQueue (x:fs,bs)) = clean (MkQueue (fs,bs))

toList :: Queue a -> [a]
toList (MkQueue (fs,bs)) = fs ++ reverse bs

instance Show a => Show (Queue a) where
  show q = show (toList q)




