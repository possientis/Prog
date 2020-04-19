{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE InstanceSigs       #-}

module  Cycled
    (   Cycled  (..)
    )   where

import Control.Lens


newtype Cycled a = Cycled [a]
    deriving Show

type instance Index (Cycled a)   = Int
type instance IxValue (Cycled a) = a

instance Ixed (Cycled a) where
    ix :: Int -> Traversal' (Cycled a) a
    ix i handler (Cycled xs) = undefined 


