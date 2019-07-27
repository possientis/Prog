{-# LANGUAGE ScopedTypeVariables    #-}

-- broken even with ScopedTypeVariables
broken :: (a -> b) -> a -> b
broken f a = result where
--  result :: b      -- 'b' is not in scope, just a new dummy type variable
    result = f a

working :: forall a b . (a -> b) -> a -> b
working f a = result where
    result :: b     -- extension + forall brings 'b' into scope
    result = f a


