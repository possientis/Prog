class Applicative f => Alternative f where
    -- | The identity of <|>
    empty :: f a
    -- | An associative binary operation
    (<|>) :: f a -> f a -> f a 
    -- | One or more
    some :: f a -> f [a]
    -- | Zero or more
    many :: f a -> f [a] 

optional :: Alternative f => f a -> f (Maybe a)
optional x = Just <$> x

instance Alternative Maybe where
    empty = Nothing
    (<|>) Nothing r = r
    (<|>) l _       = l
    some Nothing    = Nothing
    some (Just x)   = Just [x]
    many Nothing    = empty 
    many (Just x)   = Just [x]


