{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

class Stack s a | s -> a where
    empty   :: s
    push    :: s -> a -> s
    peek    :: s -> Maybe a
    isEmpty :: s -> Bool
    pop     :: s -> s
    toList  :: s -> [a]


instance Stack [a] a where
    empty       = []
    push xs x   = x : xs
    peek []     = Nothing
    peek (x:xs) = Just x
    isEmpty []  = True
    isEmpty _   = False
    pop []      = []
    pop (x:xs)  = xs
    toList      = id





