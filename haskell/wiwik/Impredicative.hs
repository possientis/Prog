{-# LANGUAGE ImpredicativeTypes #-}
--{-# LANGUAGE RankNTypes #-}

{- Can't unify Int ~ Char 
revUni :: forall a. Maybe ([a] -> [a]) -> Maybe ([Int],[Char])
revUni (Just g) = Just (g [3], g "Hello")
revUni Nothing = Nothing
-}

-- Uses higher-ranked polymorphism (need rankNTypes extension)
f :: (forall a. [a] -> a) -> (Int, Char)
f get = (get [1,2],get ['a','b','c'])


-- Uses impredicative polymorphism (need ImpredicativeTypes)
g :: Maybe (forall a. [a] -> a) -> (Int, Char)
g Nothing = (0,'0')
g (Just get) = (get [1,2], get ['a','b','c'])

