

class Functor' f where
    fmap' :: (a -> b) -> f a -> f b


class Monad' m where
    return' :: a -> m a
    bind'   :: m a -> (a -> m b) -> m b


instance Functor' ((->) r) where
    fmap' = (.)

instance Monad' ((->) r) where
    return'     = const
    bind' m k   = \r -> k (m r) r 

