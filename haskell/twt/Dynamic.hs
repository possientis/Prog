{-# LANGUAGE GADTs              #-}
{-# LANGUAGE RankNTypes         #-}

import Data.Typeable

data Dynamic where
    Dynamic :: (Typeable a) => a -> Dynamic

elimDynamic 
    :: (forall a . Typeable a => a -> r)
    -> Dynamic
    -> r
elimDynamic f (Dynamic a) = f a


fromDynamic :: Typeable a => Dynamic -> Maybe a
-- fromDynamic (Dynamic x) = cast x
fromDynamic = elimDynamic cast

liftD2
    :: forall a b r .
       ( Typeable a
       , Typeable b
       , Typeable r
       )
    => (a -> b -> r)
    -> Dynamic
    -> Dynamic
    -> Maybe Dynamic
liftD2 f x y = do
    x' <- fromDynamic x  
    y' <- fromDynamic y
    return $ Dynamic $ f x' y'

pyPlus :: Dynamic -> Dynamic -> Dynamic
pyPlus a b = undefined 


