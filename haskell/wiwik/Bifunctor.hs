class Bifunctor p where
    bimap  :: (a -> b) -> (a' -> b') -> p a a' -> p b b'
    first  :: (a -> b) -> p a c -> p b c
    second :: (a -> b) -> p c a -> p c b

instance Bifunctor (,) where
    bimap f g (x,y) = (f x, g y)
    first f (x,y)   = (f x, y)
    second f (x, y) = (x, f y)


instance Bifunctor Either where
    bimap f g (Left x)  = Left (f x)
    bimap f g (Right y) = Right (g y)
    first f (Left x)    = Left (f x)
    first f (Right y)   = Right y
    second f (Left x)   = Left x
    second f (Right y)  = Right (f y)

