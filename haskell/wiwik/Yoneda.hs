{-# LANGUAGE RankNTypes #-}

embed :: Functor f => f a -> forall b. (a -> b) -> f b
embed x f = fmap f x


unembed :: Functor f => (forall b. (a -> b) -> f b) -> f a
unembed f = f id



