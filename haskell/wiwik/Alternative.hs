import Control.Applicative hiding (Alternative, empty, (<|>), some, many)

class Applicative f => Alternative f where
    -- | The identity of <|>
    empty :: f a
    -- | An associative binary operation
    (<|>) :: f a -> f a -> f a 
    -- | One or more
    some :: f a -> f [a]
    some v = some_v where
        many_v = some_v <|> pure []
        some_v = liftA2 (:) v many_v
        
    -- | Zero or more
    many :: f a -> f [a] 
    many v = many_v where
        many_v = some_v <|> pure []
        some_v = liftA2 (:) v many_v
        

optional :: Alternative f => f a -> f (Maybe a)
optional x = Just <$> x

instance Alternative Maybe where
    empty = Nothing
    (<|>) Nothing r = r
    (<|>) l _       = l


instance Alternative [] where
    empty = []
    (<|>) = (++)

main :: IO ()
main = do
    print $ foldl1 (<|>) [Nothing,Just 5, Just 3]
