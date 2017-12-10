{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Prelude hiding (sum, zipWith, fromList)
import Data.Vector

import Test.SmallCheck
import Test.SmallCheck.Series

dot :: Num a => Vector a -> Vector a -> a
dot xs ys = sum (zipWith (*) xs ys)

cauchy :: Vector Double -> Vector Double -> Bool
cauchy xs ys = (dot xs ys)^2 <= (dot xs xs) * (dot ys ys)


instance (Serial m a, Monad m) => Serial m (Vector a) where
    series = fromList <$> series

main :: IO ()
main = smallCheck 4 cauchy  -- 5 takes too long

