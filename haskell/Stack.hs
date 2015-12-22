module Stack (Stack, push, peek, pop, isEmpty, empty, toList) where

newtype Stack a = MkStack [a]

empty :: Stack a
empty = MkStack []

push :: Stack a -> a -> Stack a
push (MkStack xs)  x = MkStack (x:xs)

peek :: Stack a -> Maybe a
peek (MkStack [])  = Nothing
peek (MkStack (x:xs)) = Just x

isEmpty :: Stack a -> Bool
isEmpty (MkStack []) = True
isEmpty _  = False

pop :: Stack a -> Stack a
pop (MkStack []) = empty
pop (MkStack (x:xs)) = MkStack xs

toList :: Stack a -> [a]
toList (MkStack xs) = xs

instance Show a => Show (Stack a) where
  show q = show (toList q)



