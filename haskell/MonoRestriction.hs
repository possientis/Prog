{-# LANGUAGE NoMonomorphismRestriction #-}
-- monomorphism restriction 

import Debug.Trace 

genericLength :: Num a => [b] -> a
genericLength []     = trace "returning from genericLength" 0
genericLength (_:xs) = 1 + genericLength xs


f :: [a] -> (Int, Integer)
f xs = (len, len) where
    len = genericLength xs
