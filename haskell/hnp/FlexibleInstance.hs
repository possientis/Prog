{-# LANGUAGE FlexibleInstances #-}
class C a where

instance C [a] where

{- LANGUAGE FlexibleInstances -}
instance C [Int]


