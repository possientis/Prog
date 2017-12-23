{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ScopedTypeVariables #-}

poly :: forall a b c. a -> b -> c -> (a,a)
poly x y z = (f x y, f x z)
    where
    -- second argument is universally quantified from inference
    -- f :: forall t0 t1. t0 -> t1 -> t0 
    f x' _ = x'


{-
mono :: forall a b c. a -> b -> c -> (a,a)
mono x y z = (f x y, f x z)
    where
    -- b is not implicitely universally quantified, because it is in scope
    -- due to the use of ScopedTypeVariables. This creates a type error
    f :: a -> b -> a
    f x' _ = x'
-}

example :: IO ()
example = do
    x :: [Int] <- readLn
    print x

