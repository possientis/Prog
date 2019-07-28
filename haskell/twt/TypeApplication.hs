{-# LANGUAGE TypeApplications   #-}


f :: (a -> b) -> (Maybe a) -> (Maybe b)
f = fmap

-- :: (a -> b) -> Maybe a -> Maybe b
g = fmap @ Maybe 

h :: Functor f => (Int -> Bool) -> f Int -> f Bool
h = fmap @_ @Int @Bool

k = show
