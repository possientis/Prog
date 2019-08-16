{-# LANGUAGE GADTs              #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}

import Data.Typeable
import Data.Maybe

data Dynamic where
    Dynamic :: (Typeable a, Show a) => a -> Dynamic

elimDynamic 
    :: (forall a . (Typeable a, Show a) => a -> r)
    -> Dynamic
    -> r
elimDynamic f (Dynamic a) = f a


fromDynamic :: (Typeable a) => Dynamic -> Maybe a
-- fromDynamic (Dynamic x) = cast x
fromDynamic = elimDynamic cast

instance Show Dynamic where
    show = elimDynamic show

liftD2
    :: forall a b r .
       ( Typeable a
       , Typeable b
       , Typeable r
       , Show r
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
pyPlus a b = fromMaybe (error "pyPLus: bad types") $ asum 
    [ liftD2 @String    @String  (++) a b
    , liftD2 @Int       @Int     (+)  a b 
    , liftD2 @String    @Int     (\s i -> s ++ show i) a b   
    , liftD2 @Int       @String  (\i s -> show i ++ s) a b
    ]

asum :: [Maybe a] -> Maybe a
asum xs = case catMaybes xs of
    []      -> Nothing
    (x:_)   -> Just x

d1 :: Dynamic
d1  = Dynamic (1::Int)

d2 :: Dynamic 
d2 =  Dynamic (2::Int)

d3 :: Dynamic 
d3 = Dynamic "hello"

d4 :: Dynamic
d4 = Dynamic "world"

main :: IO ()
main = do
    print $ pyPlus d1 d2
    print $ pyPlus d3 d4
    print $ pyPlus d1 d3
    print $ pyPlus d3 d1
    print $ pyPlus d1 (Dynamic (1::Double))
